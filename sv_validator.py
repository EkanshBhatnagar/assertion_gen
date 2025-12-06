"""
SystemVerilog Syntax Validator using Verilator

This module provides syntax validation and linting for SystemVerilog assertions
using Verilator as the backend parser.
"""
import subprocess
import tempfile
import os
import re
from pathlib import Path
from typing import Tuple, List, Optional


class SVValidationError:
    """Represents a SystemVerilog syntax error."""
    def __init__(self, line: int, message: str, severity: str = "Error"):
        self.line = line
        self.message = message
        self.severity = severity

    def __str__(self):
        return f"[{self.severity}] Line {self.line}: {self.message}"


class SVValidator:
    """
    SystemVerilog syntax validator using Verilator.

    Verilator is used to parse and lint SystemVerilog code.
    """

    def __init__(self, verilator_path: str = "verilator"):
        """
        Initialize the validator.

        Args:
            verilator_path: Path to verilator executable
        """
        self.verilator_path = verilator_path
        self._check_verilator()

    def _check_verilator(self):
        """Check if verilator is available."""
        try:
            result = subprocess.run(
                [self.verilator_path, "--version"],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode == 0:
                version = result.stdout.strip().split('\n')[0]
                print(f"✓ Found {version}")
            else:
                raise FileNotFoundError("Verilator not working")
        except (FileNotFoundError, subprocess.TimeoutExpired):
            raise FileNotFoundError(
                f"Verilator not found at '{self.verilator_path}'. "
                "Please install verilator: brew install verilator (macOS) or apt-get install verilator (Linux)"
            )

    def validate_assertion(self, assertion: str, module_context: Optional[str] = None) -> Tuple[bool, List[SVValidationError]]:
        """
        Validate a single SystemVerilog assertion.

        Args:
            assertion: The assertion string to validate
            module_context: Optional module context (parameters, signals) to include

        Returns:
            Tuple of (is_valid, list_of_errors)
        """
        # Create a minimal testbench wrapper for the assertion
        sv_code = self._create_testbench_wrapper(assertion, module_context)

        return self._validate_code(sv_code)

    def validate_testbench(self, testbench_file: Path) -> Tuple[bool, List[SVValidationError]]:
        """
        Validate a complete testbench file.

        Args:
            testbench_file: Path to the testbench file

        Returns:
            Tuple of (is_valid, list_of_errors)
        """
        if not testbench_file.exists():
            return False, [SVValidationError(0, f"File not found: {testbench_file}", "Error")]

        with open(testbench_file, 'r') as f:
            sv_code = f.read()

        return self._validate_code(sv_code)

    def _create_testbench_wrapper(self, assertion: str, module_context: Optional[str] = None) -> str:
        """
        Create a minimal testbench wrapper around an assertion for validation.

        Args:
            assertion: The assertion to wrap
            module_context: Optional context (parameters, signal declarations)

        Returns:
            Complete SystemVerilog code for validation
        """
        # Extract label if present
        label_match = re.match(r'^(\w+)\s*:\s*(.+)$', assertion.strip())
        if label_match:
            label = label_match.group(1)
            assertion_body = label_match.group(2)
        else:
            label = "test_assertion"
            assertion_body = assertion.strip()

        # Create minimal testbench
        code = f"""
module validation_tb;
    // Clock and reset
    logic clk;
    logic rst_n;

    // Default parameters (can be overridden by context)
    parameter DEPTH = 8;
    parameter DATA_WIDTH = 8;
    parameter FIFO_DEPTH = 8;

    // Common signals for FIFO/similar designs
    logic wr_en, rd_en, full, empty, almost_full, almost_empty;
    logic wr_ack, rd_ack, overflow, underflow;
    logic [DATA_WIDTH-1:0] data_in, data_out;
    logic [3:0] count;

    // Module context (if provided)
{module_context if module_context else ""}

    // DUT placeholder (for DUT.signal references)
    struct {{
        logic wr_en, rd_en, full, empty, almost_full, almost_empty;
        logic wr_ack, rd_ack, overflow, underflow;
        logic almostfull, almostempty;  // Alternate naming
        logic [DATA_WIDTH-1:0] data_in, data_out;
        logic [3:0] count;
        logic rst_n;
    }} DUT;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Assertion to validate
    {assertion_body}

endmodule
"""
        return code

    def _validate_code(self, sv_code: str) -> Tuple[bool, List[SVValidationError]]:
        """
        Validate SystemVerilog code using Verilator.

        Args:
            sv_code: The SystemVerilog code to validate

        Returns:
            Tuple of (is_valid, list_of_errors)
        """
        errors = []

        # Create temporary file for the code with consistent naming
        with tempfile.NamedTemporaryFile(mode='w', suffix='_validation_tb.sv', delete=False, prefix='') as f:
            f.write(sv_code)
            temp_file = f.name

        try:
            # Run verilator in lint-only mode
            # --lint-only: Only lint, don't compile
            # --timing: Enable timing constructs (required for assertions with delays)
            # Suppress warnings for test wrapper code (unused signals, etc.)
            result = subprocess.run(
                [
                    self.verilator_path,
                    "--lint-only",
                    "--timing",
                    "-Wno-DECLFILENAME",
                    "-Wno-UNOPTFLAT",
                    "-Wno-UNUSEDSIGNAL",
                    "-Wno-UNUSEDPARAM",
                    "-Wno-UNDRIVEN",
                    temp_file
                ],
                capture_output=True,
                text=True,
                timeout=10
            )

            # Parse verilator output
            errors = self._parse_verilator_output(result.stderr)

            # Count only actual Errors, not Warnings
            error_count = len([e for e in errors if e.severity == "Error"])

            # Valid if no ERRORS (warnings are OK)
            is_valid = (error_count == 0)

            # Return only errors (filter out warnings)
            errors_only = [e for e in errors if e.severity == "Error"]

            return is_valid, errors_only

        except subprocess.TimeoutExpired:
            return False, [SVValidationError(0, "Validation timeout", "Error")]
        finally:
            # Clean up temp file
            try:
                os.unlink(temp_file)
            except:
                pass

    def _parse_verilator_output(self, output: str) -> List[SVValidationError]:
        """
        Parse Verilator error/warning output.

        Args:
            output: Verilator stderr output

        Returns:
            List of validation errors
        """
        errors = []

        # Verilator output format: %Error: file.sv:line: message
        # or %Warning: file.sv:line: message
        pattern = r'%(\w+):\s+[^:]+:(\d+):\s+(.+)'

        for line in output.split('\n'):
            match = re.search(pattern, line)
            if match:
                severity = match.group(1)
                line_num = int(match.group(2))
                message = match.group(3).strip()

                # Filter out some common non-critical warnings
                if "Input file" in message or "Exiting" in message:
                    continue

                errors.append(SVValidationError(line_num, message, severity))

        return errors


def validate_assertion_with_feedback(assertion: str, validator: SVValidator, max_attempts: int = 1) -> Tuple[bool, str]:
    """
    Validate an assertion and provide feedback.

    Args:
        assertion: The assertion to validate
        validator: SVValidator instance
        max_attempts: Maximum validation attempts (currently just validates once)

    Returns:
        Tuple of (is_valid, feedback_message)
    """
    is_valid, errors = validator.validate_assertion(assertion)

    if is_valid:
        return True, "✓ Assertion is syntactically valid"

    # Generate feedback message
    feedback_lines = ["✗ Assertion has syntax errors:"]
    for error in errors:
        feedback_lines.append(f"  - {error}")

    return False, "\n".join(feedback_lines)


if __name__ == "__main__":
    # Test the validator
    print("SystemVerilog Validator Test")
    print("=" * 80)

    validator = SVValidator()

    # Test cases
    test_assertions = [
        # Valid assertion
        ("as__test1: assert property (@(posedge clk) wr_en |=> wr_ack);", True),

        # Invalid: wrong syntax (property before assert)
        ("as__test2: property assert (@(posedge clk) wr_en |=> wr_ack);", False),

        # Invalid: malformed from user's example
        ("assert property (as__test3 @(posedge clk) $rose(DUT.rst_n) |=> ##1 (!DUT.full));", False),

        # Valid: correct version (without ##1 which is redundant after |=>)
        ("as__test4: assert property (@(posedge clk) $rose(DUT.rst_n) |=> (!DUT.full && !DUT.almostfull));", True),
    ]

    for assertion, expected_valid in test_assertions:
        print(f"\nTesting: {assertion[:60]}...")
        is_valid, errors = validator.validate_assertion(assertion)

        status = "✓ PASS" if is_valid == expected_valid else "✗ FAIL"
        print(f"{status} - Expected: {'valid' if expected_valid else 'invalid'}, Got: {'valid' if is_valid else 'invalid'}")

        if errors:
            print("Errors:")
            for err in errors:
                print(f"  {err}")
