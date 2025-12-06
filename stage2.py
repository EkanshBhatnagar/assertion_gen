import dspy
import os
from dotenv import load_dotenv
from example_loader import load_examples_from_directory, create_few_shot_examples

class EnglishAssertionToSystemVerilog(dspy.Signature):
    """
    Given a plain English assertion statement, generate a correct SystemVerilog assertion.

    Follow these guidelines:
    1. Use proper SystemVerilog assertion syntax with 'assert property'
    2. Use temporal operators: |-> (implication), |=> (followed by), ##N (delay)
    3. Use system functions: $past, $stable, $countones, $rose, $fell
    4. Use s_eventually for liveness properties
    5. Name assertions with prefixes: as__ (assert), am__ (assume), co__ (cover)
    6. For parameterized assertions, use generate blocks
    7. Reference signals with hierarchical paths when needed (module.signal)
    """
    english_assertion = dspy.InputField(desc="A plain English assertion statement describing what to check.")
    systemverilog_assertion = dspy.OutputField(desc="A syntactically correct SystemVerilog assertion.")

def generate_sv_assertions(prompts: list[str]) -> list[str]:
    """
    Generates SystemVerilog assertions from a list of plain English assertion prompts
    using few-shot learning with high-quality examples.

    Args:
        prompts: A list of plain English assertion prompts.

    Returns:
        A list of SystemVerilog assertions.
    """
    load_dotenv()
    openrouter_api_key = os.getenv("OPENROUTER_API_KEY")

    if not openrouter_api_key:
        raise ValueError("OPENROUTER_API_KEY not found in .env file")

    lm = dspy.LM(
        model="openrouter/anthropic/claude-3-opus",
        max_tokens=2048
    )

    dspy.configure(
        lm=lm,
        api_key=openrouter_api_key,
        api_base="https://openrouter.ai/api/v1"
    )

    # Load examples from the examples directory
    print("Loading few-shot examples from examples/ directory...")
    examples_data = load_examples_from_directory()
    few_shot_examples = create_few_shot_examples(examples_data, max_examples=8)
    print(f"Using {len(few_shot_examples)} few-shot examples for assertion generation\n")

    class AssertionGenerator(dspy.Module):
        def __init__(self, examples):
            super().__init__()
            # Use ChainOfThought with few-shot examples
            self.generator = dspy.ChainOfThought(EnglishAssertionToSystemVerilog)
            self.examples = examples

        def forward(self, english_assertion):
            # DSPy will automatically use examples for few-shot prompting
            # when we pass them during prediction
            return self.generator(
                english_assertion=english_assertion,
                demos=self.examples
            )

    assertion_generator = AssertionGenerator(few_shot_examples)
    sv_assertions = []

    for i, prompt in enumerate(prompts, 1):
        if prompt.strip():
            print(f"[{i}/{len(prompts)}] Generating assertion...")
            try:
                result = assertion_generator(english_assertion=prompt)
                sv_assertions.append(result.systemverilog_assertion)
                print(f"  ✓ Generated: {result.systemverilog_assertion[:80]}...")
            except Exception as e:
                print(f"  ✗ Error: {e}")
                # Fallback: create a simple assertion
                sv_assertions.append(f"// Failed to generate assertion for: {prompt[:50]}...")

    return sv_assertions
