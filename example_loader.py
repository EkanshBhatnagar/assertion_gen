"""
Example loader for few-shot learning with SystemVerilog assertions.
Loads and parses SVA examples from the examples/ directory.
"""
import os
import re
from typing import List, Dict
from pathlib import Path
import dspy


def extract_assertions_from_file(file_path: str) -> List[str]:
    """
    Extract individual assertions from a SystemVerilog property file.

    Args:
        file_path: Path to the .sv file

    Returns:
        List of assertion strings
    """
    with open(file_path, 'r') as f:
        content = f.read()

    # Find all assertions (assert property, assume property, cover property)
    # Pattern matches both single-line and multi-line assertions
    patterns = [
        r'((?:as__|am__|co__|asgpt__)\w+\s*:\s*(?:assert|assume|cover)\s+property\s*\([^;]+\);)',
        r'((?:as__|am__|co__|asgpt__)\w+\s*:\s*(?:assert|assume|cover)\s+property\s*\([\s\S]*?\);)',
    ]

    assertions = []
    for pattern in patterns:
        matches = re.findall(pattern, content, re.MULTILINE | re.DOTALL)
        assertions.extend(matches)

    # Remove duplicates while preserving order
    seen = set()
    unique_assertions = []
    for assertion in assertions:
        # Normalize whitespace for comparison
        normalized = ' '.join(assertion.split())
        if normalized not in seen:
            seen.add(normalized)
            unique_assertions.append(assertion.strip())

    return unique_assertions


def load_examples_from_directory(examples_dir: str = "examples") -> List[Dict[str, str]]:
    """
    Load all SVA examples from the examples directory.

    Args:
        examples_dir: Path to the examples directory

    Returns:
        List of dictionaries with 'description' and 'assertion' keys
    """
    examples = []
    examples_path = Path(examples_dir)

    if not examples_path.exists():
        print(f"Warning: Examples directory '{examples_dir}' not found")
        return examples

    # Find all *_prop.sv files in subdirectories
    prop_files = list(examples_path.glob("*/sva/*_prop.sv"))

    for prop_file in prop_files:
        module_name = prop_file.stem.replace('_prop', '')
        assertions = extract_assertions_from_file(str(prop_file))

        print(f"Loaded {len(assertions)} assertions from {prop_file.name}")

        for assertion in assertions:
            # Extract assertion name from the label
            label_match = re.match(r'(\w+)\s*:', assertion)
            assertion_name = label_match.group(1) if label_match else "unnamed"

            # Create a description based on the assertion name and content
            description = f"Assertion {assertion_name} for {module_name} module"

            examples.append({
                "description": description,
                "assertion": assertion,
                "module": module_name
            })

    return examples


def create_few_shot_examples(examples: List[Dict[str, str]], max_examples: int = 8) -> List[dspy.Example]:
    """
    Convert loaded examples into DSPy Example objects for few-shot learning.

    Args:
        examples: List of example dictionaries
        max_examples: Maximum number of examples to use

    Returns:
        List of DSPy Example objects
    """
    dspy_examples = []

    # Select diverse examples (try to get from different modules)
    selected = []
    modules_seen = set()

    # First pass: get one from each module
    for ex in examples:
        if ex['module'] not in modules_seen and len(selected) < max_examples:
            selected.append(ex)
            modules_seen.add(ex['module'])

    # Second pass: fill remaining slots
    for ex in examples:
        if len(selected) >= max_examples:
            break
        if ex not in selected:
            selected.append(ex)

    # Convert to DSPy Examples
    for ex in selected[:max_examples]:
        dspy_examples.append(
            dspy.Example(
                english_assertion=ex['description'],
                systemverilog_assertion=ex['assertion']
            ).with_inputs("english_assertion")
        )

    return dspy_examples


def get_quality_assertions(examples: List[Dict[str, str]], count: int = 10) -> List[str]:
    """
    Get a selection of high-quality assertions for reference.

    Args:
        examples: List of example dictionaries
        count: Number of assertions to return

    Returns:
        List of assertion strings
    """
    # Prioritize certain patterns (generate blocks, temporal operators, etc.)
    scored_examples = []

    for ex in examples:
        score = 0
        assertion = ex['assertion']

        # Score based on quality indicators
        if 'generate' in assertion.lower():
            score += 3
        if '|=>' in assertion:
            score += 2
        if '|->' in assertion:
            score += 2
        if '$past' in assertion:
            score += 1
        if '$countones' in assertion:
            score += 1
        if 's_eventually' in assertion:
            score += 1
        if len(assertion) > 100 and len(assertion) < 500:
            score += 1

        scored_examples.append((score, ex))

    # Sort by score and return top examples
    scored_examples.sort(key=lambda x: x[0], reverse=True)
    return [ex['assertion'] for score, ex in scored_examples[:count]]


if __name__ == "__main__":
    # Test the loader
    examples = load_examples_from_directory()
    print(f"\nTotal examples loaded: {len(examples)}")

    if examples:
        print(f"\nSample assertion:")
        print(examples[0]['assertion'])

        print(f"\nQuality assertions:")
        quality = get_quality_assertions(examples, 5)
        for i, assertion in enumerate(quality, 1):
            print(f"\n{i}. {assertion[:150]}...")
