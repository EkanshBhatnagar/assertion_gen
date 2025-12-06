import dspy
import re
import os
from typing import List, Tuple
from example_loader import load_examples_from_directory, get_quality_assertions

class AssertionRefinement(dspy.Signature):
    """
    Refine a SystemVerilog assertion to match the actual RTL design signals.
    Given the human language description, the generated assertion, and RTL signal info,
    output a corrected assertion with proper signal names and syntax.

    Guidelines for refinement:
    1. Match signal names exactly to those in signal_info
    2. Use hierarchical signal references (module.signal) when needed
    3. Preserve temporal operators: |-> (implication), |=> (followed by), ##N (delay)
    4. Preserve system functions: $past, $stable, $countones, etc.
    5. Ensure proper SystemVerilog assertion syntax
    6. Keep assertion label with correct prefix (as__, am__, co__)
    7. For internal signals, use hierarchical notation like FIFO.wr_ptr

    CRITICAL - DO NOT generate malformed assertions:
    - NEVER end with just |-> or |=> without a consequent
    - NEVER use patterns like "|-> ##N;" (implication to delay with nothing after)
    - NEVER put the label inside assert property() - WRONG: "assert property (label: @(posedge clk)...)"
    - CORRECT label placement: "label: assert property (@(posedge clk)...)"
    - ALWAYS ensure complete structure: condition |-> consequent; or condition |=> consequent;
    - Examples of CORRECT assertions:
      * as__test: assert property (@(posedge clk) wr_en && !full |=> wr_ack);
      * as__full: assert property (@(posedge clk) count == DEPTH |-> full);
      * req |-> ##3 ack  (NOT "req |-> ##3;")
    - If you cannot generate a valid assertion, keep the original unchanged
    """
    human_description = dspy.InputField(desc="The original human language description of what the assertion should check")
    generated_assertion = dspy.InputField(desc="The SystemVerilog assertion that needs refinement")
    signal_info = dspy.InputField(desc="Information about module signals, ports, and internal signals")
    refined_assertion = dspy.OutputField(desc="The refined SystemVerilog assertion with correct signal names and COMPLETE, VALID syntax. Label must be OUTSIDE assert property().")


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

    # Extract parameters with types and values (deduplicate)
    params = []
    param_names_seen = set()
    param_pattern = r'parameter\s+(?:(\w+)\s+)?(\w+)\s*=\s*([^;]+);'
    matches = re.findall(param_pattern, rtl_code)
    for match in matches:
        param_type, param_name, param_value = match
        if param_name not in param_names_seen:
            param_names_seen.add(param_name)
            params.append({
                'name': param_name,
                'value': param_value.strip(),
                'type': param_type.strip() if param_type.strip() else 'int'
            })

    # Extract all port names from module declaration
    module_port_list = []
    module_decl_match = re.search(r'module\s+\w+\s*\((.*?)\);', rtl_code, re.DOTALL)
    if module_decl_match:
        port_list_str = module_decl_match.group(1)
        # Split by comma and clean up
        module_port_list = [p.strip() for p in port_list_str.split(',') if p.strip()]

    # Extract inputs (handle multiple names on one line)
    inputs = []
    input_names_seen = set()
    # Match input declarations that may have multiple signals
    input_lines = re.findall(r'input\s+(?:wire\s+|reg\s+)?(\[[\w\-:+\s\$]+\])?\s*([^;]+);', rtl_code)
    for match in input_lines:
        width, names_str = match
        # Split by comma to handle multiple signal names
        signal_names = [n.strip() for n in names_str.split(',')]
        for name in signal_names:
            if name and name not in input_names_seen:
                input_names_seen.add(name)
                inputs.append({'name': name, 'width': width.strip() if width else ''})

    # Extract outputs (handle multiple names on one line)
    outputs = []
    output_names_seen = set()
    output_lines = re.findall(r'output\s+(reg|wire)?\s*(\[[\w\-:+\s\$]+\])?\s*([^;]+);', rtl_code)
    for match in output_lines:
        out_type, width, names_str = match
        # Split by comma to handle multiple signal names
        signal_names = [n.strip() for n in names_str.split(',')]
        for name in signal_names:
            if name and name not in output_names_seen:
                output_names_seen.add(name)
                outputs.append({
                    'name': name,
                    'width': width.strip() if width else '',
                    'type': out_type if out_type else 'wire'
                })

    # Extract internal registers and wires
    internals = []
    internal_patterns = [
        r'(?:^|\n)\s*reg\s+(\[[\w\-:+\s]+\])?\s*(\w+)',
        r'(?:^|\n)\s*wire\s+(\[[\w\-:+\s]+\])?\s*(\w+)'
    ]
    output_names = [o['name'] for o in outputs]
    for pattern in internal_patterns:
        matches = re.findall(pattern, rtl_code, re.MULTILINE)
        for match in matches:
            width, name = match
            if name not in output_names and name not in [i['name'] for i in internals]:
                internals.append({
                    'name': name,
                    'width': width.strip() if width else ''
                })

    # Build all ports list
    all_ports = inputs + outputs

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

def generate_testbench_code(module_name: str, ports: List[dict], params: List[dict],
                            internals: List[dict], assertions: str) -> str:
    """
    Generate a complete testbench with DUT instantiation and assertions.

    Args:
        module_name: Name of the RTL module
        ports: List of port dictionaries with 'name' and 'width'
        params: List of parameter dictionaries with 'name', 'value', 'type'
        internals: List of internal signal dictionaries
        assertions: String containing all assertions

    Returns:
        Complete testbench code
    """
    # Generate parameter declarations
    param_decls = []
    param_assigns = []
    for p in params:
        param_decls.append(f"    parameter {p['name']} = {p['value']};")
        param_assigns.append(f"        .{p['name']}({p['name']})")

    # Generate logic declarations for ports
    port_decls = []
    port_connections = []
    for port in ports:
        width_str = f"{port['width']} " if port['width'] else ""
        port_decls.append(f"    logic {width_str}{port['name']};")
        port_connections.append(f"        .{port['name']}({port['name']})")

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
    Parse assertions from a file, properly handling multi-line assertions.

    An assertion starts with 'assert property' or 'label: assert property'
    and ends with a semicolon. Labels can be on a separate line.

    Args:
        file_content: Content of the assertions file

    Returns:
        List of complete assertions (each as a single string)
    """
    assertions = []
    lines = file_content.split('\n')
    current_assertion = []
    in_assertion = False
    pending_label = None

    for line in lines:
        stripped = line.strip()

        # Skip empty lines when not in an assertion
        if not stripped and not in_assertion:
            continue

        # Check if this is a standalone label (label: on its own line)
        label_only_match = re.match(r'^(\w+)\s*:\s*$', stripped)
        if label_only_match and not in_assertion:
            # Save this label for the next assertion
            pending_label = stripped
            continue

        # Check if this line starts an assertion
        # Patterns: "assert property" or "label: assert property"
        if re.search(r'(^\w+\s*:\s*assert\s+property)|(^assert\s+property)', stripped, re.IGNORECASE):
            # If we were already building an assertion, save it
            if in_assertion and current_assertion:
                assertions.append(' '.join(current_assertion))
                current_assertion = []

            in_assertion = True

            # If we have a pending label, prepend it
            if pending_label:
                current_assertion = [pending_label, stripped]
                pending_label = None
            else:
                current_assertion = [stripped]

            # Check if it ends on the same line
            if ';' in stripped:
                assertions.append(' '.join(current_assertion))
                current_assertion = []
                in_assertion = False

        elif in_assertion:
            # Continue building the current assertion
            current_assertion.append(stripped)

            # Check if this line ends the assertion
            if ';' in stripped:
                assertions.append(' '.join(current_assertion))
                current_assertion = []
                in_assertion = False

    # Handle case where file ended while still in assertion
    if current_assertion:
        assertions.append(' '.join(current_assertion))

    # Clean up: normalize whitespace and filter out incomplete assertions
    cleaned_assertions = []
    for assertion in assertions:
        # Normalize multiple spaces to single space
        cleaned = re.sub(r'\s+', ' ', assertion).strip()

        # Only add if it contains 'assert property' and ends with semicolon
        if cleaned and 'assert property' in cleaned.lower() and cleaned.endswith(';'):
            cleaned_assertions.append(cleaned)

    return cleaned_assertions

def generate_formal_verification_code(assertions: List[str], rtl_code: str) -> str:
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
        Complete formal verification SystemVerilog code
    """
    # Configure DSPy for LM Studio
    lm = dspy.LM(
        model="openai/gpt-oss-20b",
        api_base="http://localhost:1234/v1",
        api_key="lm-studio",
        max_tokens=2048,
        temperature=0.3
    )

    dspy.configure(lm=lm)

    # Load quality examples for few-shot learning
    print("Loading quality SVA examples for refinement...")
    examples_data = load_examples_from_directory()
    quality_examples = get_quality_assertions(examples_data, count=10)
    print(f"Loaded {len(quality_examples)} quality examples for reference\n")

    # Extract signal information from RTL
    signal_info, module_name, ports, params, internals = extract_signal_info(rtl_code)

    print(f"\nDetected module: {module_name}")
    print(f"  Parameters: {len(params)}")
    print(f"  Ports: {len(ports)}")
    print(f"  Internal signals: {len(internals)}")
    print(f"\nSignal Information:\n{signal_info}")

    # Add examples to signal info as reference
    examples_text = "\n\nReference Examples (High-Quality SVA):\n"
    for i, ex in enumerate(quality_examples[:5], 1):
        examples_text += f"{i}. {ex}\n\n"
    signal_info_with_examples = signal_info + examples_text

    # Load human language descriptions from stage 1
    human_descriptions = load_human_descriptions()
    print(f"\nLoaded {len(human_descriptions)} human language descriptions from stage 1")

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

    # Instantiate refiner
    refiner = AssertionRefiner()

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
    print("REFINING ASSERTIONS WITH SYNTAX VALIDATION")
    print("="*80)

    # Create output directory and prepare incremental output file
    output_dir = "output"
    os.makedirs(output_dir, exist_ok=True)
    progress_file = os.path.join(output_dir, "refined_assertions_progress.sv")

    # Clear the progress file at start
    with open(progress_file, "w") as f:
        f.write(f"// Refined Assertions Progress\n")
        f.write(f"// Total assertions to process: {len([a for a in assertions if clean_assertion(a).strip()])}\n")
        f.write(f"// {'='*76}\n\n")

    for i, assertion in enumerate(assertions, 1):
        assertion_clean = clean_assertion(assertion)

        # Skip empty assertions
        if not assertion_clean.strip():
            continue

        print(f"\n[{i}/{len(assertions)}] Original assertion:")
        print(f"  {assertion_clean[:100]}...")

        # Validate the original assertion from Stage 2
        original_is_valid = validate_assertion(assertion_clean)
        if not original_is_valid:
            print(f"  ⚠ Warning: Original from Stage 2 is malformed - will attempt to fix")

        # Get corresponding human description if available
        human_desc = human_descriptions[i-1] if i-1 < len(human_descriptions) else "No description available"
        print(f"  Human description: {human_desc[:80]}...")

        try:
            # Use DSPy to refine the assertion with examples
            result = refiner(
                human_description=human_desc,
                generated_assertion=assertion_clean,
                signal_info=signal_info_with_examples
            )

            refined = result.refined_assertion.strip()

            # Additional cleanup
            refined = clean_assertion(refined)
            refined = extract_assertion_from_thinking(refined)

            # Validate it's not empty after extraction
            if not refined or len(refined) < 10:
                print(f"  Warning: Extracted assertion too short")
                if original_is_valid:
                    print(f"    → Using original (valid)")
                    refined = assertion_clean
                else:
                    print(f"    → Original also invalid, skipping this assertion")
                    continue
            else:
                print(f"  Refined: {refined[:100]}...")

            # Validate the assertion is well-formed (pattern-based)
            if not validate_assertion(refined):
                print(f"  ✗ Warning: Assertion failed pattern validation (malformed)")
                if original_is_valid:
                    print(f"    → Reverting to original (valid)")
                    refined = assertion_clean
                else:
                    print(f"    → Original also invalid, skipping this assertion")
                    continue

            # Syntax validation with Verilator (if available)
            if use_validator:
                is_valid, errors = validator.validate_assertion(refined)
                if not is_valid:
                    print(f"  ✗ Syntax errors detected ({len(errors)} errors)")
                    for err in errors[:3]:  # Show first 3 errors
                        print(f"      - {err}")

                    # Try to fix syntax errors with feedback loop (max 2 attempts)
                    fix_attempt = 0
                    max_fix_attempts = 2
                    while not is_valid and fix_attempt < max_fix_attempts:
                        fix_attempt += 1
                        print(f"  🔧 Attempting syntax fix (attempt {fix_attempt}/{max_fix_attempts})...")

                        # Create error message for LLM
                        error_msg = "\n".join([f"- {err}" for err in errors[:5]])

                        try:
                            # Use DSPy to fix syntax
                            syntax_fixer = dspy.ChainOfThought(AssertionSyntaxFix)
                            fix_result = syntax_fixer(
                                original_assertion=refined,
                                syntax_errors=error_msg,
                                signal_info=signal_info
                            )

                            fixed = fix_result.fixed_assertion.strip()
                            fixed = clean_assertion(fixed)
                            fixed = extract_assertion_from_thinking(fixed)

                            # Validate the fix
                            is_valid, errors = validator.validate_assertion(fixed)
                            if is_valid:
                                print(f"  ✓ Syntax fixed successfully!")
                                refined = fixed
                                break
                            else:
                                print(f"  ⚠ Fix attempt {fix_attempt} still has errors")
                        except Exception as e:
                            print(f"  ⚠ Fix attempt {fix_attempt} failed: {e}")
                            break

                    # If still invalid after attempts, check if original is valid
                    if not is_valid:
                        print(f"  ✗ Could not fix syntax errors")
                        if original_is_valid:
                            print(f"    → Reverting to original (valid)")
                            refined = assertion_clean
                        else:
                            print(f"    → Original also invalid, skipping this assertion")
                            continue
                else:
                    print(f"  ✓ Syntax validation passed")

            # Update signal references (DUT.signal for internal signals)
            refined = update_assertion_signal_references(refined, module_name, ports, internals)
            print(f"  Updated signal references")

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

    all_assertions = "\n\n".join(assertions_indented)

    # Generate testbench code
    print("\n" + "="*80)
    print("GENERATING TESTBENCH WITH DUT INSTANTIATION")
    print("="*80)

    try:
        testbench_code = generate_testbench_code(
            module_name=module_name,
            ports=ports,
            params=params,
            internals=internals,
            assertions=all_assertions
        )
        print("✓ Testbench generated successfully")
        print(f"  - Module: {module_name}_tb")
        print(f"  - Parameters: {len(params)}")
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
{all_assertions}

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

    print(f"\nℹ️  Incremental progress available in: {progress_file}")
    return formal_code

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
