import dspy
import os
from dotenv import load_dotenv

class SpecificationToPrompts(dspy.Signature):
    """
    Given a hardware design specification, generate a list of human-language prompts 
    that can be used to generate SystemVerilog assertions.
    """
    specification = dspy.InputField(desc="The hardware design specification in Markdown format.")
    prompts = dspy.OutputField(desc="A list of human-language prompts for generating SystemVerilog assertions.")

def generate_prompts(specification_content: str) -> list[str]:
    """
    Generates prompts for creating SystemVerilog assertions from a design specification.

    Args:
        specification_content: The content of the design specification file.

    Returns:
        A list of prompts.
    """
    load_dotenv()
    openrouter_api_key = os.getenv("OPENROUTER_API_KEY")

    if not openrouter_api_key:
        raise ValueError("OPENROUTER_API_KEY not found in .env file")

    lm = dspy.LM(
        model="openrouter/anthropic/claude-3-opus",
        max_tokens=1024
    )

    dspy.configure(
        lm=lm,
        api_key=openrouter_api_key,
        api_base="https://openrouter.ai/api/v1"
    )

    # Define the program
    class AssertionPromptGenerator(dspy.Module):
        def __init__(self):
            super().__init__()
            self.generator = dspy.ChainOfThought(SpecificationToPrompts)

        def forward(self, specification):
            return self.generator(specification=specification)

    # Instantiate and run the program
    prompt_generator = AssertionPromptGenerator()
    result = prompt_generator(specification=specification_content)
    
    # Extract the prompts as a list of strings
    prompts_list = result.prompts.strip().split('\n')
    
    return prompts_list
