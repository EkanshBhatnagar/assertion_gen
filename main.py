import argparse
import os
from stage1 import generate_prompts

def main():
    parser = argparse.ArgumentParser(description="Generate assertion prompts from a design specification.")
    parser.add_argument("spec_path", help="Path to the design specification file.")
    args = parser.parse_args()

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


if __name__ == "__main__":
    main()
