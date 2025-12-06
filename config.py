"""
Configuration file for assertion generation pipeline.
Stores paths and settings for all stages.
"""
from pathlib import Path
from typing import Optional
import os


class Config:
    """Configuration for assertion generation pipeline."""

    def __init__(self):
        # Project root directory
        self.project_root = Path(__file__).parent

        # Design files
        self.rtl_top_module = "FIFO"  # Name of the top-level module
        self.rtl_design_file = self.project_root / "design" / "FIFO.sv"  # Path to RTL file
        self.spec_file = self.project_root / "design" / "specification.md"  # Specification file

        # Output directories
        self.output_dir = self.project_root / "output"
        self.output_dir.mkdir(exist_ok=True)

        # Output files
        self.prompts_file = self.output_dir / "assertion_prompts.txt"
        self.assertions_file = self.output_dir / "generated_assertions.sv"
        self.testbench_file = self.output_dir / "formal_verification.sv"
        self.tcl_file = self.output_dir / "jaspergold_fpv.tcl"
        self.progress_file = self.output_dir / "refined_assertions_progress.sv"

        # Examples directory
        self.examples_dir = self.project_root / "examples"

        # API Configuration
        self.openrouter_api_key = os.getenv("OPENROUTER_API_KEY")
        self.lm_studio_base_url = "http://localhost:1234/v1"
        self.lm_studio_model = "openai/gpt-oss-20b"

        # Model settings
        self.stage1_model = "openrouter/anthropic/claude-3-opus"
        self.stage2_model = "openrouter/anthropic/claude-3-opus"
        self.stage3_model = self.lm_studio_model  # Local model
        self.stage4_model = self.lm_studio_model  # Local model

        # Clock and reset signals (extracted from RTL or specified)
        self.clock_signal = "clk"
        self.reset_signal = "rst_n"
        self.reset_active_low = True  # True if reset is active low

        # JasperGold settings
        self.prove_time_limit = "72h"
        self.proofgrid_max_jobs = 180

    def set_design(self, rtl_file: str, top_module: Optional[str] = None,
                   spec_file: Optional[str] = None):
        """
        Set the design files for the pipeline.

        Args:
            rtl_file: Path to the RTL design file
            top_module: Name of the top-level module (extracted from RTL if not provided)
            spec_file: Path to the specification file (optional)
        """
        self.rtl_design_file = Path(rtl_file)

        if not self.rtl_design_file.exists():
            raise FileNotFoundError(f"RTL file not found: {rtl_file}")

        if top_module:
            self.rtl_top_module = top_module
        else:
            # Try to extract module name from RTL file
            with open(self.rtl_design_file, 'r') as f:
                content = f.read()
                import re
                match = re.search(r'module\s+(\w+)', content)
                if match:
                    self.rtl_top_module = match.group(1)
                else:
                    raise ValueError("Could not extract module name from RTL. Please specify top_module.")

        if spec_file:
            self.spec_file = Path(spec_file)

    def set_clock_reset(self, clock: str, reset: str, reset_active_low: bool = True):
        """
        Set clock and reset signal names.

        Args:
            clock: Clock signal name
            reset: Reset signal name
            reset_active_low: True if reset is active low
        """
        self.clock_signal = clock
        self.reset_signal = reset
        self.reset_active_low = reset_active_low

    def get_reset_expression(self) -> str:
        """
        Get the reset expression for JasperGold.

        Returns:
            Reset expression string
        """
        if self.reset_active_low:
            return f"(!{self.reset_signal})"
        else:
            return self.reset_signal

    def __str__(self) -> str:
        """String representation of configuration."""
        return f"""Configuration:
  RTL Top Module: {self.rtl_top_module}
  RTL Design File: {self.rtl_design_file}
  Specification File: {self.spec_file}
  Output Directory: {self.output_dir}
  Clock Signal: {self.clock_signal}
  Reset Signal: {self.reset_signal} (active {'low' if self.reset_active_low else 'high'})
"""


# Global configuration instance
config = Config()


if __name__ == "__main__":
    print("Current Configuration:")
    print(config)
