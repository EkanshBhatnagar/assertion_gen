#!/usr/bin/env python3
"""
Main pipeline for SystemVerilog assertion generation and formal verification.

This script orchestrates all four stages:
1. Generate assertion prompts from specification
2. Generate SystemVerilog assertions from prompts
3. Generate testbench with DUT instantiation
4. Generate JasperGold TCL script

Usage:
    python main.py --all                    # Run all stages
    python main.py --stage 1                # Run specific stage
    python main.py --stage 2 3 4            # Run multiple stages
    python main.py --rtl design/FIFO.sv     # Specify custom RTL file
"""

import argparse
import sys
import os
import json
from pathlib import Path
from dotenv import load_dotenv

# Import configuration
from config import config

# Import stage modules
from stage1 import generate_prompts
from stage2 import generate_sv_assertions
from stage3 import generate_formal_verification_code
from stage4 import generate_jaspergold_tcl


def print_banner(stage: int, description: str):
    """Print a formatted banner for each stage."""
    print("\n" + "="*80)
    print(f" STAGE {stage}: {description}")
    print("="*80 + "\n")


def run_stage1() -> bool:
    """
    Stage 1: Generate assertion prompts from specification.

    Returns:
        True if successful, False otherwise
    """
    print_banner(1, "Generate Assertion Prompts from Specification")

    try:
        # Read specification
        with open(config.spec_file, "r") as f:
            specification_content = f.read()

        print(f"📖 Reading specification from: {config.spec_file}")
        print(f"   Specification length: {len(specification_content)} characters\n")

        # Generate prompts
        prompts = generate_prompts(specification_content)

        # Save prompts
        with open(config.prompts_file, "w") as f:
            for prompt in prompts:
                f.write(f"{prompt}\n")

        print(f"\n✓ Stage 1 completed successfully")
        print(f"  Generated {len(prompts)} assertion prompts")
        print(f"  Saved to: {config.prompts_file}\n")
        return True

    except FileNotFoundError as e:
        print(f"✗ Error: Specification file not found: {config.spec_file}")
        print(f"  Please ensure the specification file exists.")
        return False
    except Exception as e:
        print(f"✗ Error in Stage 1: {e}")
        return False


def run_stage2() -> bool:
    """
    Stage 2: Generate SystemVerilog assertions from prompts.

    Returns:
        True if successful, False otherwise
    """
    print_banner(2, "Generate SystemVerilog Assertions from Prompts")

    try:
        # Load prompts from Stage 1
        with open(config.prompts_file, "r") as f:
            prompts = [line.strip() for line in f.readlines() if line.strip()]

        print(f"📖 Reading prompts from: {config.prompts_file}")
        print(f"   Number of prompts: {len(prompts)}\n")

        if not prompts:
            print("✗ Error: No prompts found. Please run Stage 1 first.")
            return False

        # Generate assertions
        sv_assertions = generate_sv_assertions(prompts)

        # Save assertions
        with open(config.assertions_file, "w") as f:
            for assertion in sv_assertions:
                f.write(f"{assertion}\n\n")

        print(f"\n✓ Stage 2 completed successfully")
        print(f"  Generated {len(sv_assertions)} SystemVerilog assertions")
        print(f"  Saved to: {config.assertions_file}\n")
        return True

    except FileNotFoundError:
        print(f"✗ Error: Prompts file not found: {config.prompts_file}")
        print(f"  Please run Stage 1 first.")
        return False
    except Exception as e:
        print(f"✗ Error in Stage 2: {e}")
        return False


def run_stage3() -> bool:
    """
    Stage 3: Generate testbench with DUT instantiation and refined assertions.

    Returns:
        True if successful, False otherwise
    """
    print_banner(3, "Generate Testbench with DUT Instantiation")

    try:
        # Load assertions from Stage 2 (properly handle multi-line assertions)
        with open(config.assertions_file, "r") as f:
            file_content = f.read()

        from stage3 import parse_assertions_from_file
        assertions = parse_assertions_from_file(file_content)

        # Load RTL code
        with open(config.rtl_design_file, "r") as f:
            rtl_code = f.read()

        print(f"📖 Reading assertions from: {config.assertions_file}")
        print(f"   Number of assertions parsed: {len(assertions)}")
        print(f"📖 Reading RTL from: {config.rtl_design_file}")
        print(f"   RTL length: {len(rtl_code)} characters\n")

        if not assertions:
            print("✗ Error: No assertions found. Please run Stage 2 first.")
            return False

        # Generate formal verification code (testbench)
        formal_code, params = generate_formal_verification_code(assertions, rtl_code)

        # Save testbench
        with open(config.testbench_file, "w") as f:
            f.write(formal_code)

        # Save parameters for stage 4
        param_file = config.output_dir / "parameters.json"
        with open(param_file, "w") as f:
            json.dump(params, f, indent=4)


        print(f"\n✓ Stage 3 completed successfully")
        print(f"  Generated testbench: {config.testbench_file}")
        print(f"  Saved parameters to: {param_file}")
        print(f"  Progress file: {config.progress_file}\n")
        return True

    except FileNotFoundError as e:
        print(f"✗ Error: Required file not found")
        print(f"  Assertions file: {config.assertions_file} - Run Stage 2 first")
        print(f"  RTL file: {config.rtl_design_file} - Check configuration")
        return False
    except Exception as e:
        print(f"✗ Error in Stage 3: {e}")
        return False


def run_stage4() -> bool:
    """
    Stage 4: Generate JasperGold TCL script.

    Returns:
        True if successful, False otherwise
    """
    print_banner(4, "Generate JasperGold TCL Script")

    try:
        # Check testbench exists
        if not config.testbench_file.exists():
            print(f"✗ Error: Testbench file not found: {config.testbench_file}")
            print(f"  Please run Stage 3 first.")
            return False

        # Load parameters from stage 3
        param_file = config.output_dir / "parameters.json"
        params_str = ""
        if param_file.exists():
            with open(param_file, "r") as f:
                params = json.load(f)
            params_str = ",".join([f"{p['name']}={p['value']}" for p in params])
            print(f"📖 Loaded {len(params)} parameters from {param_file}")

        # Generate TCL script
        top_module = f"{config.rtl_top_module}_tb"
        tcl_script = generate_jaspergold_tcl(
            top_module=top_module,
            rtl_file=config.rtl_design_file,
            testbench_file=config.testbench_file,
            clock_signal=config.clock_signal,
            reset_expression=config.get_reset_expression(),
            parameters=params_str
        )

        # Save TCL script
        with open(config.tcl_file, "w") as f:
            f.write(tcl_script)

        print(f"\n✓ Stage 4 completed successfully")
        print(f"  Generated TCL script: {config.tcl_file}")
        print(f"\n  To run formal verification:")
        print(f"    jaspergold {config.tcl_file}\n")
        return True

    except Exception as e:
        print(f"✗ Error in Stage 4: {e}")
        return False


def main():
    """Main entry point for the pipeline."""
    parser = argparse.ArgumentParser(
        description="SystemVerilog Assertion Generation and Formal Verification Pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python main.py --all                    # Run all stages
  python main.py --stage 1 2 3 4          # Run all stages
  python main.py --stage 2                # Run only stage 2
  python main.py --stage 3 4              # Run stages 3 and 4
  python main.py --rtl design/UART.sv --top UART --all
        """
    )

    parser.add_argument(
        "--stage",
        type=int,
        nargs="+",
        choices=[1, 2, 3, 4],
        help="Specific stage(s) to run"
    )

    parser.add_argument(
        "--all",
        action="store_true",
        help="Run all stages"
    )

    parser.add_argument(
        "--rtl",
        type=str,
        help="Path to RTL design file"
    )

    parser.add_argument(
        "--top",
        type=str,
        help="Name of top-level module"
    )

    parser.add_argument(
        "--spec",
        type=str,
        help="Path to specification file"
    )

    parser.add_argument(
        "--clock",
        type=str,
        help="Clock signal name (default: clk)"
    )

    parser.add_argument(
        "--reset",
        type=str,
        help="Reset signal name (default: rst_n)"
    )

    parser.add_argument(
        "--reset-active-high",
        action="store_true",
        help="Reset is active high (default: active low)"
    )

    args = parser.parse_args()

    # Load environment variables
    load_dotenv()

    # Update configuration if custom paths provided
    if args.rtl:
        config.set_design(args.rtl, args.top, args.spec)
    elif args.top:
        config.rtl_top_module = args.top

    if args.spec:
        config.spec_file = Path(args.spec)

    if args.clock:
        config.clock_signal = args.clock

    if args.reset:
        config.reset_signal = args.reset
        config.reset_active_low = not args.reset_active_high

    # Display configuration
    print("\n" + "="*80)
    print(" ASSERTION GENERATION PIPELINE")
    print("="*80)
    print(config)

    # Determine which stages to run
    stages_to_run = []
    if args.all:
        stages_to_run = [1, 2, 3, 4]
    elif args.stage:
        stages_to_run = sorted(args.stage)
    else:
        print("Error: Please specify --stage or --all")
        parser.print_help()
        return 1

    print(f"Stages to run: {', '.join(map(str, stages_to_run))}\n")

    # Run stages
    stage_functions = {
        1: run_stage1,
        2: run_stage2,
        3: run_stage3,
        4: run_stage4
    }

    failed_stages = []
    for stage_num in stages_to_run:
        success = stage_functions[stage_num]()
        if not success:
            failed_stages.append(stage_num)
            print(f"\n⚠️  Stage {stage_num} failed. Stopping pipeline.")
            break

    # Summary
    print("\n" + "="*80)
    print(" PIPELINE SUMMARY")
    print("="*80)

    if not failed_stages:
        print("✓ All stages completed successfully!\n")
        print("Generated files:")
        if 1 in stages_to_run:
            print(f"  Stage 1: {config.prompts_file}")
        if 2 in stages_to_run:
            print(f"  Stage 2: {config.assertions_file}")
        if 3 in stages_to_run:
            print(f"  Stage 3: {config.testbench_file}")
            print(f"           {config.progress_file}")
        if 4 in stages_to_run:
            print(f"  Stage 4: {config.tcl_file}")
        print()
        return 0
    else:
        print(f"✗ Failed stages: {', '.join(map(str, failed_stages))}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
