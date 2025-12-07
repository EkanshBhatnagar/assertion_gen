"""
Stage 4: JasperGold TCL Script Generation

Generates a TCL script for JasperGold formal verification tool using few-shot learning.
Uses local LM Studio model with examples from the examples directory.
"""
import dspy
import os
from pathlib import Path
from typing import List
from example_loader import load_tcl_examples, create_tcl_few_shot_prompt
from config import config


class JasperGoldTCLGeneration(dspy.Signature):
    """
    Generate a JasperGold TCL script for formal verification.

    The TCL script should include:
    1. analyze -clear and analyze -sv12 commands to load RTL and testbench (use RELATIVE paths)
    2. elaborate command with -top flag and -create_related_covers (NO -auto_hr_info flag).
       DO NOT use the `-param` switch as parameters are already specified in the formal testbench.
    3. clock command to specify the clock signal
    4. reset command with expression for reset signal
    5. get_design_info to check complexity
    6. Proof settings (set_word_level_reduction, set_prove_time_limit, etc.)
    7. prove -all command (NOT autoprove -all -bg) to run formal verification
    8. report command to show results

    IMPORTANT CORRECTIONS:
    - Use RELATIVE file paths (e.g., design/FIFO.sv, not /absolute/path/to/design/FIFO.sv)
    - Use "prove -all" NOT "autoprove -all -bg"
    - In elaborate: use "-create_related_covers {witness precondition}" but NO "-auto_hr_info"
    - DO NOT use -param flag in elaborate command (parameters are in the testbench)

    Follow the patterns shown in the reference examples.
    """
    top_module = dspy.InputField(desc="Name of the top-level testbench module")
    rtl_file = dspy.InputField(desc="Relative path to the RTL design file (e.g., design/FIFO.sv)")
    testbench_file = dspy.InputField(desc="Relative path to the testbench file (e.g., output/formal_verification.sv)")
    parameters = dspy.InputField(desc="Comma-separated parameter assignments for the top-level module (e.g., 'WIDTH=8,DEPTH=32'). Can be empty.")
    clock_signal = dspy.InputField(desc="Name of the clock signal")
    reset_signal = dspy.InputField(desc="Name and expression for reset signal")
    reference_examples = dspy.InputField(desc="Reference TCL examples for guidance")
    tcl_script = dspy.OutputField(desc="Complete JasperGold TCL script with RELATIVE paths and 'prove -all' command")


def generate_jaspergold_tcl(top_module: str, rtl_file: Path, testbench_file: Path,
                            clock_signal: str, reset_expression: str, parameters: str = "") -> str:
    """
    Generate a JasperGold TCL script for formal verification.

    Args:
        top_module: Name of the top-level testbench module (e.g., "FIFO_tb")
        rtl_file: Path to the RTL design file
        testbench_file: Path to the testbench file
        clock_signal: Name of the clock signal
        reset_expression: Reset expression (e.g., "(!rst_n)" for active-low reset)
        parameters: Comma-separated parameter values for the top-level module.

    Returns:
        Complete TCL script as a string
    """
    # Load TCL examples for few-shot learning
    print("Loading JasperGold TCL examples...")
    tcl_examples = load_tcl_examples()
    print(f"Loaded {len(tcl_examples)} TCL examples for reference\n")

    if not tcl_examples:
        print("Warning: No TCL examples found, generating from template")
        return generate_tcl_template(top_module, rtl_file, testbench_file,
                                    clock_signal, reset_expression, parameters)

    # Create reference prompt with examples
    reference_prompt = create_tcl_few_shot_prompt(tcl_examples)

    # Configure DSPy for LM Studio
    lm = dspy.LM(
        model=config.stage4_model,
        api_base=config.lm_studio_base_url,
        api_key="lm-studio",
        max_tokens=2048,
        temperature=0.2  # Lower temperature for more deterministic output
    )

    dspy.configure(lm=lm)

    # Define DSPy module
    class TCLGenerator(dspy.Module):
        def __init__(self):
            super().__init__()
            self.generator = dspy.ChainOfThought(JasperGoldTCLGeneration)

        def forward(self, top_module, rtl_file, testbench_file,
                   clock_signal, reset_signal, parameters, reference_examples):
            return self.generator(
                top_module=top_module,
                rtl_file=str(rtl_file),
                testbench_file=str(testbench_file),
                clock_signal=clock_signal,
                reset_signal=reset_signal,
                parameters=parameters,
                reference_examples=reference_examples
            )

    # Generate TCL script
    print("="*80)
    print("GENERATING JASPERGOLD TCL SCRIPT")
    print("="*80)
    print(f"  Top module: {top_module}")
    print(f"  RTL file: {rtl_file}")
    print(f"  Testbench: {testbench_file}")
    print(f"  Clock: {clock_signal}")
    print(f"  Reset: {reset_expression}")
    if parameters:
        print(f"  Parameters: {parameters}")
    print()

    try:
        generator = TCLGenerator()
        result = generator(
            top_module=top_module,
            rtl_file=rtl_file,
            testbench_file=testbench_file,
            clock_signal=clock_signal,
            reset_signal=reset_expression,
            parameters=parameters,
            reference_examples=reference_prompt
        )

        tcl_script = result.tcl_script.strip()

        # Clean up any markdown code fences
        import re
        tcl_script = re.sub(r'```tcl\s*', '', tcl_script)
        tcl_script = re.sub(r'```\s*', '', tcl_script)

        print("✓ TCL script generated successfully")
        return tcl_script

    except Exception as e:
        print(f"✗ Error generating TCL script: {e}")
        print("  Falling back to template generation")
        return generate_tcl_template(top_module, rtl_file, testbench_file,
                                    clock_signal, reset_expression, parameters)


def generate_tcl_template(top_module: str, rtl_file: Path, testbench_file: Path,
                         clock_signal: str, reset_expression: str, parameters: str = "") -> str:
    """
    Generate a basic TCL script template without LLM generation.

    Args:
        top_module: Name of the top-level testbench module
        rtl_file: Path to the RTL design file
        testbench_file: Path to the testbench file
        clock_signal: Name of the clock signal
        reset_expression: Reset expression
        parameters: Comma-separated parameter values.

    Returns:
        TCL script string
    """
    # Convert paths to relative if possible
    try:
        rtl_rel = rtl_file.relative_to(Path.cwd())
        tb_rel = testbench_file.relative_to(Path.cwd())
    except ValueError:
        # If can't make relative, just use the path as-is
        rtl_rel = rtl_file
        tb_rel = testbench_file

    tcl_script = f"""# JasperGold TCL Script for Formal Verification
# Auto-generated by assertion generation pipeline
# Module: {top_module}

# Clear previous analysis
analyze -clear

# Configure analysis settings
set_elaborate_single_run_mode off
set_automatic_library_search on
set_analyze_libunboundsearch on
set_analyze_librescan on

# Analyze RTL design
analyze -sv12 {rtl_rel}

# Analyze testbench with assertions
analyze -sv12 {tb_rel}

# Elaborate the design
elaborate -top {top_module} -create_related_covers {{witness precondition}}

# Set up clock
clock {clock_signal}

# Set up reset
reset -expression {reset_expression}

# Get design information
get_design_info

# Configure proof settings
set_word_level_reduction on
set_prove_time_limit {config.prove_time_limit}

# Optional: Configure proof grid (uncomment if using grid computing)
# set_proofgrid_max_jobs {config.proofgrid_max_jobs}
# set_proofgrid_manager on

# Run formal verification
prove -all

# Generate report
report
"""

    return tcl_script


if __name__ == "__main__":
    # Test TCL generation
    print("Stage 4: JasperGold TCL Script Generation")
    print("="*80)

    # Use configuration
    from config import config

    top_module = f"{config.rtl_top_module}_tb"
    rtl_file = config.rtl_design_file
    testbench_file = config.testbench_file
    clock_signal = config.clock_signal
    reset_expression = config.get_reset_expression()

    # Generate TCL script
    tcl_script = generate_jaspergold_tcl(
        top_module=top_module,
        rtl_file=rtl_file,
        testbench_file=testbench_file,
        clock_signal=clock_signal,
        reset_expression=reset_expression
    )

    # Save to file
    output_file = config.tcl_file
    with open(output_file, "w") as f:
        f.write(tcl_script)

    print(f"\n✓ TCL script saved to: {output_file}")
    print(f"\nTo run formal verification:")
    print(f"  jaspergold {output_file}")
