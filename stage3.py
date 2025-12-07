import dspy
import re
import os
from typing import List, Tuple
from example_loader import load_examples_from_directory, get_quality_assertions
from config import config

class SimpleAssertionFix(dspy.Signature):
    """
    You are a SystemVerilog expert. Your task is to fix signal names in a given SystemVerilog construct.
    You MUST follow these rules strictly.

    **Rules:**
    1.  **PRESERVE `generate` BLOCKS**: If the input is a `generate` block, the `generate...endgenerate` keywords and structure MUST be preserved in the output. DO NOT strip them.
    2.  **ONLY FIX SIGNAL NAMES**: Your ONLY job is to replace incorrect signal names with the correct ones from the provided `available_signals` list.
    3.  **DO NOT CHANGE LOGIC**: Do not alter the logic of the assertion or the block.
    4.  **DO NOT CHANGE TEMPORAL OPERATORS**: Do not change `|=>`, `|->`, `##N`, etc.
    5.  **DO NOT CHANGE LABELS**: Preserve all assertion or block labels (e.g., `my_label:`).

    **Input Format:**
    - `original_assertion`: The SystemVerilog code (can be a single `assert` or a full `generate` block).
    - `available_signals`: A comma-separated list of valid signal names from the RTL.

    **Output Format:**
    - `fixed_assertion`: The corrected SystemVerilog code, with ONLY the signal names fixed and the original structure (especially `generate` blocks) preserved.
    """
    original_assertion = dspy.InputField(desc="The assertion or generate block with possibly wrong signal names")
    available_signals = dspy.InputField(desc="List of ACTUAL signal names in the RTL design")
    fixed_assertion = dspy.OutputField(desc="The construct with ONLY signal names fixed, preserving the exact original structure")


class AssertionSyntaxFix(dspy.Signature):
    """
    Fix SystemVerilog assertion syntax errors based on validator feedback.

    You are given an assertion that failed syntax validation and the specific errors found.
    Your job is to fix ONLY the syntax errors while preserving the assertion's intent and logic.

    Common syntax errors to fix:
    1. Label inside assert property: "assert property (label: @..." -> "label: assert property (@..."
    2. Missing semicolon at end
    3. Unbalanced parentheses
    4. Incorrect temporal operator usage
    5. Invalid delay syntax (##N should be followed by consequent)

    DO NOT change the assertion logic or signals - only fix syntax!
    """
    original_assertion = dspy.InputField(desc="The assertion with syntax errors")
    syntax_errors = dspy.InputField(desc="Specific syntax errors found by the validator")
    signal_info = dspy.InputField(desc="Available signals for reference")
    fixed_assertion = dspy.OutputField(desc="The assertion with syntax errors fixed, preserving original logic")

def extract_signal_info(rtl_code: str) -> tuple:
    """
    Extract comprehensive signal information from RTL code.

    Args:
        rtl_code: The RTL design code

    Returns:
        Tuple of (signal_info_string, module_name, port_list, param_list, internal_signals)
    """
    # Extract module name
    module_match = re.search(r'module\s+(\w+)', rtl_code)
    module_name = module_match.group(1) if module_match else "unknown"

    params = []
    param_names_seen = set()

    # 1. Find parameters in module header, e.g., # (parameter WIDTH = 8)
    module_header_match = re.search(r'module\s+\w+\s*#\s*\((.*?)\)', rtl_code, re.DOTALL)
    if module_header_match:
        param_block_str = module_header_match.group(1)
        # Pattern for "parameter TYPE NAME = VALUE" or "parameter NAME = VALUE"
        header_param_pattern = r'parameter\s+(?:\w+\s+)?(\w+)\s*=\s*([^,)]+)'
        for match in re.findall(header_param_pattern, param_block_str):
            param_name, param_value = match
            if param_name not in param_names_seen:
                param_names_seen.add(param_name)
                # For simplicity, type is inferred as 'int' when not specified
                params.append({
                    'name': param_name,
                    'value': param_value.strip(),
                    'type': 'int' 
                })

    # 2. Find parameters declared directly in the module body (Verilog-2001 style)
    # To avoid parsing outside the main module, we first get the module body
    module_body_match = re.search(r'module\s+\w+\s*.*?;(.*?)endmodule', rtl_code, re.DOTALL)
    if module_body_match:
        module_body = module_body_match.group(1)
        body_param_pattern = r'^\s*parameter\s+(?:(\w+)\s+)?(\w+)\s*=\s*([^;]+);'
        for match in re.findall(body_param_pattern, module_body, re.MULTILINE):
            param_type, param_name, param_value = match
            if param_name not in param_names_seen:
                param_names_seen.add(param_name)
                params.append({
                    'name': param_name,
                    'value': param_value.strip(),
                    'type': param_type.strip() if param_type.strip() else 'int'
                })

    # Extract port declarations (input, output)
    inputs = []
    outputs = []
    all_ports = [] # To store all port dictionaries

    port_list_str = ""
    port_list_match = re.search(r'module\s+\w+\s*(?:#\s*\(.*?\))?\s*\((.*?)\);', rtl_code, re.DOTALL)
    if port_list_match:
        port_list_str = port_list_match.group(1)

    if port_list_str:
        # Split by comma to get individual port declarations
        individual_ports = [p.strip() for p in port_list_str.split(',') if p.strip()]

        for port_decl in individual_ports:
            # Try to match input ports
            input_match = re.match(r'input\s+(?:logic|wire|reg)?\s*(\[[\w\-:+\s\$]+\])?\s*(\w+)', port_decl)
            if input_match:
                width = input_match.group(1)
                name = input_match.group(2)
                inputs.append({'name': name, 'width': width.strip() if width else ''})
                all_ports.append({'name': name, 'width': width.strip() if width else '', 'direction': 'input'})
                continue

            # Try to match output ports
            output_match = re.match(r'output\s+(?:logic|wire|reg)?\s*(\[[\w\-:+\s\$]+\])?\s*(\w+)', port_decl)
            if output_match:
                width = output_match.group(1)
                name = output_match.group(2)
                outputs.append({'name': name, 'width': width.strip() if width else ''})
                all_ports.append({'name': name, 'width': width.strip() if width else '', 'direction': 'output'})
                continue

            # If it's not explicitly input/output, it might be an inout or implicitly declared
            # For simplicity, we'll try to extract just the name if not matched yet
            name_match = re.match(r'(?:logic|wire|reg)?\s*(\[[\w\-:+\s\$]+\])?\s*(\w+)', port_decl)
            if name_match:
                width = name_match.group(1)
                name = name_match.group(2)
                # If not already added as input/output, assume it's part of all_ports for now
                if name not in {p['name'] for p in all_ports}:
                    all_ports.append({'name': name, 'width': width.strip() if width else '', 'direction': 'inout/implicit'})

    # Extract internal registers and wires
    internals = []
    # Collect all port names for exclusion from internal signals
    port_names_set = {p['name'] for p in all_ports}
    
    internal_patterns = [
        r'(?:^|\n)\s*reg\s+(\[[\w\-:+\s]+\])?\s*(\w+)\s*[^;]*;',
        r'(?:^|\n)\s*wire\s+(\[[\w\-:+\s]+\])?\s*(\w+)\s*[^;]*;'
    ]
    if module_body_match:
        module_body_for_internals = module_body_match.group(1)
        for pattern in internal_patterns:
            matches = re.findall(pattern, module_body_for_internals, re.MULTILINE)
            for match in matches:
                width, name = match
                # Ensure it's not a port or a parameter
                if name not in port_names_set and name not in param_names_seen and name not in {i['name'] for i in internals}:
                    internals.append({
                        'name': name,
                        'width': width.strip() if width else ''
                    })

    signal_info = f"""
Module: {module_name}

Parameters:
{', '.join([f"{p['name']}={p['value']}" for p in params]) if params else "None"}

Input Ports:
{', '.join([f"{i['name']} {i['width']}" if i['width'] else i['name'] for i in inputs]) if inputs else "None"}

Output Ports:
{', '.join([f"{o['name']} {o['width']}" if o['width'] else o['name'] for o in outputs]) if outputs else "None"}

Internal Signals (access via DUT.signal_name in assertions):
{', '.join([f"{s['name']} {s['width']}" if s['width'] else s['name'] for s in internals]) if internals else "None"}
"""
    return signal_info, module_name, all_ports, params, internals

def clean_assertion(assertion: str) -> str:
    """
    Clean up assertion by removing markdown code fences and extra formatting.

    Args:
        assertion: Raw assertion string

    Returns:
        Cleaned assertion string
    """
    # Remove markdown code fences
    assertion = re.sub(r'```systemverilog\s*', '', assertion)
    assertion = re.sub(r'```\s*', '', assertion)

    # Remove backticks
    assertion = assertion.strip('`').strip()

    # Fix common spacing issues
    assertion = re.sub(r'\|-\s*>', '|->', assertion)

    return assertion

def validate_assertion(assertion: str) -> bool:
    """
    Validate that an assertion is well-formed.

    Args:
        assertion: The assertion string to validate

    Returns:
        True if valid, False otherwise
    """
    # If the assertion is a generate block, skip strict validation
    if assertion.strip().lower().startswith('generate') and 'endgenerate' in assertion.lower():
        return True

    # Must contain 'assert' and end with semicolon
    if 'assert' not in assertion.lower():
        return False

    if not assertion.strip().endswith(';'):
        return False

    # Check for malformed patterns
    malformed_patterns = [
        r'\|->\s*##\d+\s*\)?;',  # |-> ##N); (implication to delay with no consequent)
        r'\|=>\s*##\d+\s*\)?;',  # |=> ##N); (similar issue)
        r'\|->\s*\)?;',          # |-> ); (implication with no consequent)
        r'\|=>\s*\)?;',          # |=> ); (similar issue)
        r'property\s*\(\s*\)',  # empty property
        r'@\(posedge\s+\w+\)\s*;',  # Ends right after clock edge: @(posedge clk);
        r'@\(posedge\s+\w+\)\s*$',  # Ends right after clock edge (no semicolon)
        r'property\s*\(\s*@\(posedge\s+\w+\)\s*\)',  # property (@(posedge clk)) - no condition
        r'disable\s+iff\s*\([^)]*\)\s*;',  # disable iff (...); - nothing after
        r'disable\s+iff\s*\([^)]*\)\s*$',  # disable iff (...) - ends abruptly
    ]

    for pattern in malformed_patterns:
        if re.search(pattern, assertion):
            return False

    # Check for incomplete property structure
    # An assertion should have actual logic after the timing spec
    # Look for property with @(posedge...) that doesn't have a condition/implication
    if 'property' in assertion.lower():
        # After @(posedge clk) and optional disable iff, there should be some logic
        # Match: property ( @(posedge clk) <optional disable iff> <MUST HAVE LOGIC HERE> )

        # Strip to check if there's actual content after timing specs
        stripped = assertion
        # Remove label if present
        stripped = re.sub(r'^\w+\s*:\s*', '', stripped)
        # Remove 'assert property'
        stripped = re.sub(r'assert\s+property\s*\(', '', stripped, flags=re.IGNORECASE)
        # Remove clock spec
        stripped = re.sub(r'@\(posedge\s+\w+\)', '', stripped)
        # Remove disable iff
        stripped = re.sub(r'disable\s+iff\s*\([^)]+\)', '', stripped)
        # Remove closing paren and semicolon
        stripped = re.sub(r'\)\s*;?\s*$', '', stripped)

        # After all that, there should be meaningful content left
        stripped = stripped.strip()
        if not stripped or len(stripped) < 3:  # Too short to be meaningful
            return False

        # Check if it only contains whitespace, parens, and semicolons
        if re.match(r'^[\s();]*$', stripped):
            return False

    # Check for balanced parentheses
    open_count = assertion.count('(')
    close_count = assertion.count(')')
    if open_count != close_count:
        return False

    return True


def extract_assertion_from_thinking(output: str) -> str:
    """
    Extract the actual SystemVerilog assertion from thinking model output.
    Thinking models output reasoning first, then the actual code.

    Args:
        output: Raw output from the thinking model

    Returns:
        Extracted assertion code
    """
    # Try to find SystemVerilog code blocks first
    code_block_match = re.search(r'```(?:systemverilog)?\s*(.*?)```', output, re.DOTALL)
    if code_block_match:
        extracted = code_block_match.group(1).strip()
        if validate_assertion(extracted):
            return extracted

    # Look for complete assertions with better patterns
    # Updated to better handle multi-line assertions
    assertion_patterns = [
        # Match: label: assert property (@(posedge clk) disable iff (...) condition |-> consequent);
        r'(\w+\s*:\s*assert\s+property\s*\((?:[^;])+;)',
        # Match: assert property (@(posedge clk) ...) with balanced parens
        r'(assert\s+property\s*\((?:[^()]|\([^()]*\))*\)\s*;)',
        # Match multi-line: captures everything from assert to semicolon
        r'(assert\s+property\s*\([\s\S]*?\)\s*;)',
        # Named properties
        r'(property\s+\w+\s*;[\s\S]*?endproperty[\s\S]*?assert\s+property[^;]+;)',
    ]

    for pattern in assertion_patterns:
        match = re.search(pattern, output, re.MULTILINE | re.DOTALL)
        if match:
            extracted = match.group(1).strip()
            # Normalize whitespace for multi-line assertions
            extracted = re.sub(r'\s+', ' ', extracted)
            if validate_assertion(extracted):
                return extracted

    # Try to extract multi-line assertions
    lines = output.split('\n')
    assertion_lines = []
    in_assertion = False

    for line in lines:
        # Skip thinking/comment blocks
        if '<thinking>' in line.lower() or '</thinking>' in line.lower():
            continue
        if line.strip().startswith('//'):
            continue

        # Start of assertion
        if 'assert' in line.lower() and 'property' in line.lower():
            in_assertion = True
            assertion_lines = [line]
        elif in_assertion:
            assertion_lines.append(line)
            if ';' in line:
                # End of assertion
                combined = ' '.join(assertion_lines)
                if validate_assertion(combined):
                    return combined.strip()
                in_assertion = False
                assertion_lines = []

    # Fallback: return the cleaned original if it validates
    cleaned = clean_assertion(output)
    if validate_assertion(cleaned):
        return cleaned

    # Last resort: return as-is (will be caught downstream)
    return cleaned

def generate_testbench_code(module_name: str, ports: List[dict], all_params: List[dict],
                            dut_params: List[dict], internals: List[dict], assertions: str) -> str:
    """
    Generate a complete testbench with DUT instantiation and assertions.

    Args:
        module_name: Name of the RTL module.
        ports: List of port dictionaries.
        all_params: All parameters for the testbench (DUT + assertion-specific).
        dut_params: Parameters specific to the DUT for instantiation.
        internals: List of internal signal dictionaries.
        assertions: String containing all assertions.

    Returns:
        Complete testbench code.
    """
    # Generate parameter declarations for all parameters in the testbench body
    param_decls = [f"    parameter {p['name']} = {p['value']};" for p in all_params]

    # Generate parameter assignments ONLY for DUT-specific parameters
    param_assigns = [f"        .{p['name']}({p['name']})" for p in dut_params]

    # Generate logic declarations for ports
    port_decls = [f"    logic {port['width'] if port['width'] else ''}{port['name']};" for port in ports]
    port_connections = [f"        .{port['name']}({port['name']})" for port in ports]

    # Build testbench
    testbench = f"""////////////////////////////////////////////////////////////////////////////////
// Testbench for {module_name}
// Auto-generated by assertion generation pipeline
// Contains DUT instantiation and formal verification assertions
////////////////////////////////////////////////////////////////////////////////

module {module_name}_tb;

    // Parameters
{chr(10).join(param_decls) if param_decls else "    // No parameters"}

    // Port declarations (as logic)
{chr(10).join(port_decls)}

    // DUT Instantiation
    {module_name} #(
{(',' + chr(10)).join(param_assigns) if param_assigns else ''}
    ) DUT (
{(',' + chr(10)).join(port_connections)}
    );

    // Default clocking and reset handling
    default clocking cb @(posedge clk);
    endclocking

    default disable iff (!rst_n);

    // Formal Verification Assertions
{assertions}

endmodule
"""
    return testbench


def validate_signals_exist(assertion: str, ports: List[dict], internals: List[dict]) -> Tuple[bool, List[str]]:
    """
    Check if all signals referenced in an assertion actually exist in the design.

    Args:
        assertion: The assertion string
        ports: List of port dictionaries
        internals: List of internal signal dictionaries

    Returns:
        Tuple of (all_signals_exist, list_of_undefined_signals)
    """
    # Get all valid signal names
    port_names = {p['name'] for p in ports}
    internal_names = {s['name'] for s in internals}
    all_valid_signals = port_names | internal_names

    # Remove the label if present (label: assert property...)
    assertion_no_label = re.sub(r'^\w+\s*:\s*', '', assertion)

    # Extract potential signal references from assertion
    # Look for identifiers (word characters) that could be signals
    # Skip SystemVerilog keywords and system functions
    sv_keywords = {'assert', 'property', 'posedge', 'negedge', 'iff', 'disable', 'throughout'}
    sv_functions = {'past', 'rose', 'fell', 'stable', 'countones'} # System functions that don't start with '$'
    sv_system_tasks_functions_with_dollar = {'onehot', 'onehot0', 'changed', 'stable', 'past', 'fell', 'rose', 'isunknown'} # Common system functions that start with '$'
    # Common references that are not signals but should not be flagged as undefined
    common_ignored_identifiers = {'clk', 'rst_n', 'DUT', 'fifo', 'FIFO', 'i', 'b1', 'WIDTH', 'NUM_REQS', 'CLIENTS', 'FIFO_WIDTH', 'FIFO_DEPTH'} # Added i, b1, WIDTH, NUM_REQS, CLIENTS

    # Find all identifiers in the assertion, including those starting with '$'
    identifiers = re.findall(r'\b[\w$]+\b', assertion_no_label)

    undefined_signals = []
    for identifier in identifiers:
        # Skip if it's a keyword, function, or looks like a parameter
        if identifier in sv_keywords:
            continue
        if identifier in sv_functions:
            continue

        # Handle SystemVerilog system functions (e.g., $onehot0, $changed)
        if identifier.startswith('$'):
            # Check if the part after '$' is a known system function
            if identifier[1:] in sv_system_tasks_functions_with_dollar:
                continue
            # If it starts with $ but is not in our known list, we'll assume it's a valid system task/function
            # to avoid false positives in signal validation.
            continue
        elif identifier in sv_system_tasks_functions_with_dollar:
            # Handle cases where the '$' might have been stripped during LLM generation or parsing
            continue

        if identifier.isupper() and identifier in common_ignored_identifiers:  # Likely a parameter or genvar that we explicitly ignore
            continue
        if identifier.isdigit():  # Numeric literal
            continue
        if identifier in common_ignored_identifiers:  # Common references that are not signals or already handled (like 'i', 'WIDTH', etc.)
            continue
        # Skip assertion labels (start with as__, am__, co__)
        if identifier.startswith(('as__', 'am__', 'co__')):
            continue
        if identifier.startswith('`'): # Compiler directives often start with backtick
            continue

        # Check if it's a valid signal
        if identifier not in all_valid_signals:
            if identifier not in undefined_signals:
                undefined_signals.append(identifier)

        # Check if it's a valid signal
        if identifier not in all_valid_signals:
            if identifier not in undefined_signals:
                undefined_signals.append(identifier)

    return (len(undefined_signals) == 0, undefined_signals)


def update_assertion_signal_references(assertion: str, module_name: str,
                                       ports: List[dict], internals: List[dict]) -> str:
    """
    Update signal references in assertions to use correct hierarchical paths.
    Port signals can be referenced directly, internal signals need DUT. prefix.

    Args:
        assertion: The assertion string
        module_name: Name of the module
        ports: List of port dictionaries
        internals: List of internal signal dictionaries

    Returns:
        Updated assertion with correct signal references
    """
    port_names = {p['name'] for p in ports}
    internal_names = {s['name'] for s in internals}

    # Replace references to internal signals with DUT.signal
    # But don't replace if already has DUT. or module. prefix
    updated = assertion

    for sig_name in internal_names:
        # Create regex pattern that matches the signal name but not when preceded by DUT. or module_name.
        # Use word boundaries to avoid partial matches
        pattern = r'(?<!DUT\.)(?<!\w)' + re.escape(sig_name) + r'(?!\w)'

        # Check if this signal is referenced in the assertion
        if re.search(pattern, updated):
            # Replace with DUT.signal_name
            updated = re.sub(pattern, f'DUT.{sig_name}', updated)

    # Also handle old-style module.signal references and convert to DUT.signal
    updated = re.sub(rf'\b{re.escape(module_name)}\.', 'DUT.', updated)

    # Handle lowercase module name references (common mistake)
    if module_name:
        updated = re.sub(rf'\b{re.escape(module_name.lower())}\.', 'DUT.', updated)

    return updated


def load_human_descriptions(prompts_file: str = "output/assertion_prompts.txt") -> List[str]:
    """
    Load human language descriptions from stage 1.

    Args:
        prompts_file: Path to the assertion prompts file

    Returns:
        List of human language descriptions
    """
    try:
        with open(prompts_file, "r") as f:
            descriptions = [line.strip() for line in f.readlines() if line.strip()]
        return descriptions
    except FileNotFoundError:
        print(f"Warning: Could not find {prompts_file}, proceeding without human descriptions")
        return []


def parse_assertions_from_file(file_content: str) -> List[str]:
    """
    Parse assertions from a file, assuming they are separated by double newlines.

    Args:
        file_content: Content of the assertions file

    Returns:
        List of complete assertions (each as a single string)
    """
    raw_assertion_blocks = file_content.split('\n\n')
    cleaned_assertions = []

    for block in raw_assertion_blocks:
        cleaned = block.strip()
        if cleaned: # Only add if the block is not empty after stripping
            cleaned_assertions.append(cleaned)

    return cleaned_assertions

def generate_formal_verification_code(assertions: List[str], rtl_code: str) -> Tuple[str, List[dict]]:
    """
    Generates formal verification code using locally hosted LM Studio model (gpt-oss-20b).
    This includes:
    1. Refining assertions to match actual RTL signals using few-shot learning
    2. Fixing syntax errors based on high-quality examples
    3. Generating auxiliary code (assertion module, bind statements)

    Args:
        assertions: List of SystemVerilog assertions from stage 2
        rtl_code: The RTL design code

    Returns:
        A tuple containing:
        - Complete formal verification SystemVerilog code (str)
        - A list of all parameters used in the testbench (List[dict])
    """
    # Configure DSPy for LM Studio
    lm = dspy.LM(
        model="openai/verireason-codellama-7b-rtlcoder-verilog-grpo-reasoning-tb",
        api_base="http://localhost:1234/v1",
        api_key="lm-studio",
        max_tokens=2048,
        temperature=0.3,
        response_format={"type": "text"} # Explicitly set response format
    )

    dspy.configure(lm=lm)

    # Load quality examples for few-shot learning
    print("Loading quality SVA examples for refinement...")
    examples_data = load_examples_from_directory()
    quality_examples = get_quality_assertions(examples_data, count=10)
    print(f"Loaded {len(quality_examples)} quality examples for reference\n")

    # Extract signal information from RTL to get DUT-specific parameters
    signal_info, module_name, ports, dut_params, internals = extract_signal_info(rtl_code)

    print(f"\nDetected module: {module_name}")
    print(f"  DUT Parameters: {len(dut_params)}")
    print(f"  Ports: {len(ports)}")
    print(f"  Internal signals: {len(internals)}")
    print(f"\nSignal Information:\n{signal_info}")

    # Load human language descriptions from stage 1
    human_descriptions = load_human_descriptions()
    print(f"\nLoaded {len(human_descriptions)} human language descriptions from stage 1")

    # --- Parameter Extraction Step ---
    assertion_params = []
    assertions_no_params = []
    for assertion in assertions:
        lines = assertion.split('\n')
        assertion_only_lines = []
        for line in lines:
            stripped_line = line.strip()
            if stripped_line.startswith("// parameter:"):
                param_decl = stripped_line.replace("// parameter:", "").strip()
                match = re.search(r'parameter\s+(\w+)\s*=\s*([^;]+);', param_decl)
                if match:
                    param_name = match.group(1)
                    param_value = match.group(2).strip()
                    # Avoid duplicates
                    if not any(p['name'] == param_name for p in assertion_params):
                        assertion_params.append({'name': param_name, 'value': param_value, 'type': 'int'})
            else:
                assertion_only_lines.append(line)
        assertions_no_params.append("\n".join(assertion_only_lines))

    # Define DSPy module for assertion refinement
    class AssertionRefiner(dspy.Module):
        def __init__(self):
            super().__init__()
            self.refine = dspy.ChainOfThought(AssertionRefinement)

        def forward(self, human_description, generated_assertion, signal_info):
            return self.refine(
                human_description=human_description,
                generated_assertion=generated_assertion,
                signal_info=signal_info
            )

    # Create simple signal list for LLM
    all_signal_names = [p['name'] for p in ports] + [s['name'] for s in internals]
    signals_list = "Available signals: " + ", ".join(all_signal_names)

    # Define simple signal fixer
    signal_fixer = dspy.ChainOfThought(SimpleAssertionFix)

    # Initialize validator for syntax checking
    try:
        from sv_validator import SVValidator
        validator = SVValidator()
        print("✓ SystemVerilog validator initialized (Verilator)")
        use_validator = True
    except Exception as e:
        print(f"⚠ Warning: Could not initialize validator: {e}")
        print("  Continuing without syntax validation")
        use_validator = False

    # Refine each assertion
    refined_assertions = []
    print("\n" + "="*80)
    print("FIXING SIGNAL NAMES AND VALIDATING")
    print("="*80)

    # Create output directory and prepare incremental output file
    output_dir = "output"
    os.makedirs(output_dir, exist_ok=True)
    progress_file = os.path.join(output_dir, "refined_assertions_progress.sv")

    # Clear the progress file at start
    with open(progress_file, "w") as f:
        f.write(f"// Refined Assertions Progress\n")
        f.write(f"// Total assertions to process: {len([a for a in assertions_no_params if clean_assertion(a).strip()])}\n")
        f.write(f"// {'='*76}\n\n")

    for i, assertion in enumerate(assertions_no_params, 1):
        assertion_clean = clean_assertion(assertion)

        # Skip empty assertions
        if not assertion_clean.strip():
            continue

        print(f"\n[{i}/{len(assertions_no_params)}] Original assertion:")
        print(f"  {assertion_clean[:100]}...")

        # Validate the original assertion from Stage 2
        original_is_valid = validate_assertion(assertion_clean)
        if not original_is_valid:
            print(f"  ⚠ Warning: Original from Stage 2 is malformed - will attempt to fix")

        # Get corresponding human description if available
        human_desc = human_descriptions[i-1] if i-1 < len(human_descriptions) else "No description available"
        print(f"  Human description: {human_desc[:80]}...")

        try:
            # Simple approach: Just fix signal names using RTL context
            result = signal_fixer(
                original_assertion=assertion_clean,
                available_signals=signals_list
            )

            refined = result.fixed_assertion.strip()
            refined = clean_assertion(refined)
            refined = extract_assertion_from_thinking(refined)

            if not refined or len(refined) < 10:
                print(f"  ⚠ Signal fix produced empty result, using original")
                refined = assertion_clean
            else:
                print(f"  Signal names fixed: {refined[:80]}...")

            # Validate the assertion is well-formed (pattern-based)
            if not validate_assertion(refined):
                print(f"  ✗ Pattern validation failed")
                if original_is_valid:
                    refined = assertion_clean
                else:
                    print(f"  ⚠ Skipping (invalid pattern)")
                    continue

            # Update signal references (DUT.signal for internal signals)
            refined = update_assertion_signal_references(refined, module_name, ports, internals)
            print(f"  Updated signal references")

            # Validate that all signals exist in the design
            signals_exist, undefined = validate_signals_exist(refined, ports, internals)
            if not signals_exist:
                print(f"  ✗ Warning: Assertion references undefined signals: {', '.join(undefined)}")
                if original_is_valid:
                    # Check if original also has undefined signals
                    original_signals_exist, _ = validate_signals_exist(assertion_clean, ports, internals)
                    if original_signals_exist:
                        print(f"    → Reverting to original (has valid signals)")
                        refined = assertion_clean
                    else:
                        print(f"    → Original also has undefined signals, skipping this assertion")
                        continue
                else:
                    print(f"    → Original also invalid, skipping this assertion")
                    continue
            
            # WORKAROUND for LLM stripping generate blocks
            # If the original was a generate block and the refined one is not, re-wrap it.
            if assertion_clean.lower().startswith('generate') and not refined.lower().startswith('generate'):
                print("  ✓ Re-wrapping stripped generate block...")
                # Extract the full generate and for loop structure
                # This is more robust than the previous implementation.
                gen_for_match = re.search(r'generate\s+for\s*\(.*?\)\s*begin', assertion_clean, re.DOTALL)
                if gen_for_match:
                    refined = f"{gen_for_match.group(0)}\n        {refined}\n    end\n    endgenerate"
                else:
                    # Check if the refined assertion uses array indexing (e.g., gnt[i], req[i])
                    # If so, it needs a proper for loop
                    if re.search(r'\[\s*i\s*\]', refined):
                        print("    → Detected array indexing [i], adding for loop...")
                        # Default for loop - use NUM_REQS or CLIENTS parameter
                        # Try to infer the parameter from the signal context
                        for_loop = "for (genvar i = 0; i < NUM_REQS; i++) begin"
                        refined = f"generate\n        {for_loop}\n        {refined}\n    end\n    endgenerate"
                    else:
                        # Fallback for generate without for loop
                        refined = f"generate\n        {refined}\n    endgenerate"

                print(f"    → Re-wrapped: {refined[:100]}...")

            # Final validation after signal updates
            if not validate_assertion(refined):
                print(f"  ✗ Warning: Assertion invalid after signal updates")
                if original_is_valid:
                    print(f"    → Reverting to original (valid)")
                    refined = assertion_clean
                else:
                    print(f"    → Original also invalid, skipping this assertion")
                    continue

            # Final syntax check after signal updates (if validator available)
            if use_validator:
                is_valid_final, _ = validator.validate_assertion(refined)
                if not is_valid_final:
                    print(f"  ✗ Warning: Syntax errors after signal updates")
                    if original_is_valid:
                        print(f"    → Reverting to original (valid)")
                        refined = assertion_clean
                    else:
                        print(f"    → Original also invalid, skipping this assertion")
                        continue

            refined_assertions.append(refined)

            # Write to progress file immediately after each assertion
            with open(progress_file, "a") as f:
                f.write(f"// Assertion {len(refined_assertions)}\n")
                f.write(f"// Human description: {human_desc}\n")
                f.write(f"{refined}\n\n")

            print(f"  ✓ Saved to progress file")

        except Exception as e:
            print(f"  Error refining assertion: {e}")

            # Only keep original if it's valid
            if original_is_valid:
                print(f"    → Using original (valid)")
                refined_assertions.append(assertion_clean)

                # Write to progress file
                with open(progress_file, "a") as f:
                    f.write(f"// Assertion {len(refined_assertions)} (error, using original)\n")
                    f.write(f"// Human description: {human_desc}\n")
                    f.write(f"{assertion_clean}\n\n")
            else:
                print(f"    → Original also invalid, skipping this assertion")

                # Write to progress file as skipped
                with open(progress_file, "a") as f:
                    f.write(f"// Assertion SKIPPED (invalid)\n")
                    f.write(f"// Human description: {human_desc}\n")
                    f.write(f"// Original: {assertion_clean}\n")
                    f.write(f"// Reason: Both original and refined assertions failed validation\n\n")

    print(f"\n✓ Progress saved to: {progress_file}")

    # Combine all refined assertions with proper indentation
    assertions_indented = []
    for assertion in refined_assertions:
        # Indent each line of the assertion
        lines = assertion.split('\n')
        indented_lines = ['    ' + line if line.strip() else '' for line in lines]
        assertions_indented.append('\n'.join(indented_lines))

    all_assertions_str = "\n\n".join(assertions_indented)

    # --- Combine Parameters ---
    all_params = list(dut_params)
    all_param_names = {p['name'] for p in all_params}
    for p in assertion_params:
        if p['name'] not in all_param_names:
            all_params.append(p)
            all_param_names.add(p['name'])
            print(f"  Discovered and added new assertion parameter: {p['name']}={p['value']}")

    # Generate testbench code
    print("\n" + "="*80)
    print("GENERATING TESTBENCH WITH DUT INSTANTIATION")
    print("="*80)

    try:
        testbench_code = generate_testbench_code(
            module_name=module_name,
            ports=ports,
            all_params=all_params,
            dut_params=dut_params,
            internals=internals,
            assertions=all_assertions_str
        )
        print("✓ Testbench generated successfully")
        print(f"  - Module: {module_name}_tb")
        print(f"  - Parameters: {len(all_params)}")
        print(f"  - Ports: {len(ports)}")
        print(f"  - DUT instance: DUT")
        print(f"  - Assertions: {len(refined_assertions)}")
    except Exception as e:
        print(f"✗ Error generating testbench: {e}")
        # Fallback: create minimal testbench
        testbench_code = f"""
module {module_name}_tb;
    // TODO: Manual testbench generation failed
    // Error: {e}

    // DUT instantiation here

    // Assertions
{all_assertions_str}

endmodule
"""

    # Final output
    formal_code = f"""////////////////////////////////////////////////////////////////////////////////
// Formal Verification Testbench for {module_name}
// Generated by Multi-Stage Assertion Generator - Stage 3
//
// This testbench includes:
// - All module parameters
// - All ports declared as logic
// - DUT instantiation ({module_name} as DUT)
// - Refined assertions with correct signal references
// - Internal signals accessed via DUT.signal_name
// - Default clocking and reset handling
//
// Note: Incremental progress saved to: output/refined_assertions_progress.sv
////////////////////////////////////////////////////////////////////////////////

{testbench_code.strip()}

////////////////////////////////////////////////////////////////////////////////
// End of Formal Verification Testbench
////////////////////////////////////////////////////////////////////////////////
"""

    print(f"\nℹ️  Incremental progress available in: {config.progress_file}")
    return formal_code, all_params

if __name__ == "__main__":
    # Test the module independently
    print("Stage 3: Formal Verification Code Generator")
    print("Using locally hosted LM Studio with gpt-oss-20b")

    # Load assertions from stage 2
    try:
        with open("output/generated_assertions.sv", "r") as f:
            file_content = f.read()
        assertions = parse_assertions_from_file(file_content)
        print(f"\nParsed {len(assertions)} assertions from Stage 2 output")
    except FileNotFoundError:
        print("Error: generated_assertions.sv not found. Please run stage 2 first.")
        exit(1)

    # Load RTL code
    try:
        with open("design/FIFO.sv", "r") as f:
            rtl_code = f.read()
    except FileNotFoundError:
        print("Error: FIFO.sv not found.")
        exit(1)

    # Generate formal verification code
    formal_code = generate_formal_verification_code(assertions, rtl_code)

    # Save output
    os.makedirs("output", exist_ok=True)
    final_output_file = "output/formal_verification.sv"
    with open(final_output_file, "w") as f:
        f.write(formal_code)

    print(f"\n{'='*80}")
    print("FILES GENERATED:")
    print(f"  1. {final_output_file}")
    print(f"     (Complete formal verification code with auxiliary module)")
    print(f"  2. output/refined_assertions_progress.sv")
    print(f"     (Incremental progress - updated after each assertion)")
    print(f"{'='*80}")
