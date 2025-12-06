import argparse
import os
from stage1 import generate_prompts
from stage2 import generate_sv_assertions
from stage3 import generate_formal_verification_code

def main():
    parser = argparse.ArgumentParser(description="Generate assertion prompts, SystemVerilog assertions, or formal verification code.")
    parser.add_argument("--stage", type=int, choices=[1, 2, 3], required=True, help="Stage 1: Generate prompts. Stage 2: Generate assertions. Stage 3: Generate formal verification code.")
    parser.add_argument("--spec_path", help="Path to the design specification file (required for stage 1).")
    args = parser.parse_args()

    if args.stage == 1:
        if not args.spec_path:
            parser.error("--spec_path is required for stage 1.")
        try:
            with open(args.spec_path, "r") as f:
                specification_content = f.read()
        except FileNotFoundError:
            print(f"Error: The file '{args.spec_path}' was not found.")
            return

        print("Generating assertion prompts...")
        prompts = generate_prompts(specification_content)

        output_dir = "output"
        os.makedirs(output_dir, exist_ok=True)

        output_file_path = os.path.join(output_dir, "assertion_prompts.txt")
        with open(output_file_path, "w") as f:
            for prompt in prompts:
                f.write(f"{prompt}\n")

        print(f"Assertion prompts saved to '{output_file_path}'")

    elif args.stage == 2:
        prompts_file = "output/assertion_prompts.txt"
        try:
            with open(prompts_file, "r") as f:
                prompts = f.readlines()
        except FileNotFoundError:
            print(f"Error: The file '{prompts_file}' was not found. Please run stage 1 first.")
            return

        print("Generating SystemVerilog assertions...")
        sv_assertions = generate_sv_assertions(prompts)

        output_dir = "output"
        os.makedirs(output_dir, exist_ok=True)

        output_file_path = os.path.join(output_dir, "generated_assertions.sv")
        with open(output_file_path, "w") as f:
            for assertion in sv_assertions:
                f.write(f"{assertion}\n\n")

        print(f"SystemVerilog assertions saved to '{output_file_path}'")

    elif args.stage == 3:
        assertions_file = "output/generated_assertions.sv"
        rtl_file = "design/FIFO.sv"
        try:
            with open(assertions_file, "r") as f:
                assertions = f.readlines()
        except FileNotFoundError:
            print(f"Error: The file '{assertions_file}' was not found. Please run stage 2 first.")
            return
        
        try:
            with open(rtl_file, "r") as f:
                rtl_code = f.read()
        except FileNotFoundError:
            print(f"Error: The file '{rtl_file}' was not found.")
            return

        print("Generating formal verification code...")
        formal_code = generate_formal_verification_code(assertions, rtl_code)

        output_dir = "output"
        os.makedirs(output_dir, exist_ok=True)

        output_file_path = os.path.join(output_dir, "formal_verification.sv")
        with open(output_file_path, "w") as f:
            f.write(formal_code)

        print(f"\nFormal verification code saved to '{output_file_path}'")
        print(f"Incremental progress available in '{output_dir}/refined_assertions_progress.sv'")


if __name__ == "__main__":
    main()
