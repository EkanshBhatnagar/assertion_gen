import dspy
import os
from dotenv import load_dotenv
from example_loader import load_examples_from_directory, create_few_shot_examples

class EnglishAssertionToSystemVerilog(dspy.Signature):
    """
    Given a plain English assertion statement, generate a correct SystemVerilog assertion.

    Follow these guidelines:
    1. Use proper SystemVerilog assertion syntax with 'assert property'

    2. **CRITICAL - Choose correct temporal operator based on timing:**
       - |-> (SAME cycle): When condition and result happen SIMULTANEOUSLY/IMMEDIATELY
         Keywords: "same cycle", "immediately", "when", "if", "implies"
         Example: "When count equals depth, full is high" -> (count == DEPTH) |-> full

       - |=> (NEXT cycle): When result happens ONE CLOCK CYCLE AFTER condition
         Keywords: "next cycle", "next clock", "following cycle", "on next", "after one cycle"
         Example: "When wr_en is high, wr_ack should be high next cycle" -> wr_en |=> wr_ack

       - ##N: When result happens N CLOCK CYCLES AFTER condition
         Keywords: "N cycles later", "after N cycles"
         Example: "2 cycles after req, ack is high" -> req ##2 ack

    3. **Parse timing keywords carefully:**
       - "next" = |=> (one cycle delay)
       - No timing word + continuous/combinational logic = |-> (same cycle)

    4. Use system functions: $past, $stable, $countones, $rose, $fell
    5. Use s_eventually for liveness properties
    6. Name assertions with prefixes: as__ (assert), am__ (assume), co__ (cover)
    7. For parameterized assertions, use generate blocks
    8. Reference signals with hierarchical paths when needed (module.signal)
    """
    english_assertion = dspy.InputField(desc="A plain English assertion describing what to check. ANALYZE timing keywords: 'next' = |=>, 'immediately/when' = |->, 'N cycles' = ##N")
    systemverilog_assertion = dspy.OutputField(desc="A syntactically correct SystemVerilog assertion with CORRECT temporal operator.")

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

    # Filter examples to include good timing operator usage
    # Prioritize examples with |=> for demonstrating next-cycle logic
    timing_examples = [ex for ex in examples_data if '|=>' in ex['assertion']]
    other_examples = [ex for ex in examples_data if '|=>' not in ex['assertion']]

    # Mix: 5 examples with |=> and 3 without
    prioritized_examples = timing_examples[:5] + other_examples[:3]
    few_shot_examples = create_few_shot_examples(prioritized_examples if prioritized_examples else examples_data, max_examples=8)

    print(f"Using {len(few_shot_examples)} few-shot examples for assertion generation")
    print(f"  - {len([ex for ex in prioritized_examples[:8] if '|=>' in ex['assertion']])} examples with |=> (next cycle)")
    print(f"  - {len([ex for ex in prioritized_examples[:8] if '|->' in ex['assertion'] and '|=>' not in ex['assertion']])} examples with |-> (same cycle)\n")

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
