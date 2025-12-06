# SystemVerilog Syntax Validation and Feedback Loop

## Problem

Stage 3 was generating assertions with incorrect syntax, such as:

```systemverilog
// WRONG: Label inside assert property()
assert property (as__fifo_reset_full_almostfull @(posedge clk)
    $rose(DUT.rst_n) |=> ##1 (!DUT.full && !DUT.almostfull));

// CORRECT: Label before assert property
as__fifo_reset_full_almostfull: assert property (@(posedge clk)
    $rose(DUT.rst_n) |=> (!DUT.full && !DUT.almostfull));
```

The LLM was making syntax errors that our pattern-based validation couldn't catch.

## Solution: Verilator-Based Syntax Validation with Feedback Loop

Integrated Verilator as a syntax validator with an automated feedback loop to fix errors.

### Architecture

```
Stage 2 Assertions
       ↓
Stage 3 Refinement (LLM)
       ↓
Pattern Validation (regex-based)
       ↓
Syntax Validation (Verilator) ← FEEDBACK LOOP
       ↓              ↓ (if errors found)
    [PASS]        [FAIL] → Extract errors
       ↓              ↓
       ↓         Syntax Fix (LLM with error feedback)
       ↓              ↓
       ↓         Re-validate (Verilator)
       ↓              ↓
       ↓         [PASS] or [FAIL after 2 attempts]
       ↓              ↓
Signal Reference Updates
       ↓
Final Syntax Validation
       ↓
Testbench Generation
```

## Implementation

### 1. SystemVerilog Validator (`sv_validator.py`)

Created a validator using Verilator as the backend parser:

```python
class SVValidator:
    """SystemVerilog syntax validator using Verilator."""

    def validate_assertion(self, assertion: str) -> Tuple[bool, List[SVValidationError]]:
        """
        Validate a single SystemVerilog assertion.

        Returns:
            Tuple of (is_valid, list_of_errors)
        """
        # Create minimal testbench wrapper
        sv_code = self._create_testbench_wrapper(assertion)

        # Run Verilator lint
        result = subprocess.run([
            "verilator",
            "--lint-only",
            "--timing",  # Enable assertions with delays
            "-Wno-UNUSEDSIGNAL",  # Suppress wrapper warnings
            temp_file
        ], ...)

        # Parse errors
        errors = self._parse_verilator_output(result.stderr)
        is_valid = (result.returncode == 0) and (no errors)

        return is_valid, errors
```

**Key Features:**
- Creates minimal testbench wrapper around assertion
- Uses Verilator's `--lint-only` mode for fast syntax checking
- Supports timing constructs (`##N` delays, `|=>`)
- Suppresses irrelevant warnings from test wrapper
- Returns structured error messages

### 2. Assertion Syntax Fix Signature (DSPy)

Created a new DSPy signature specifically for fixing syntax errors:

```python
class AssertionSyntaxFix(dspy.Signature):
    """
    Fix SystemVerilog assertion syntax errors based on validator feedback.

    Common syntax errors to fix:
    1. Label inside assert property: "assert property (label: @..."
       → "label: assert property (@..."
    2. Missing semicolon at end
    3. Unbalanced parentheses
    4. Incorrect temporal operator usage
    5. Invalid delay syntax

    DO NOT change the assertion logic or signals - only fix syntax!
    """
    original_assertion = dspy.InputField()
    syntax_errors = dspy.InputField()  # Errors from Verilator
    signal_info = dspy.InputField()
    fixed_assertion = dspy.OutputField()
```

This signature focuses the LLM on fixing ONLY syntax, not logic.

### 3. Feedback Loop Integration in Stage 3

Added validation checkpoints in the refinement pipeline:

```python
# After initial refinement
if use_validator:
    is_valid, errors = validator.validate_assertion(refined)
    if not is_valid:
        print(f"✗ Syntax errors detected ({len(errors)} errors)")

        # Feedback loop (max 2 attempts)
        for attempt in range(2):
            # Create error message for LLM
            error_msg = "\n".join([f"- {err}" for err in errors[:5]])

            # Use DSPy to fix syntax
            syntax_fixer = dspy.ChainOfThought(AssertionSyntaxFix)
            fix_result = syntax_fixer(
                original_assertion=refined,
                syntax_errors=error_msg,
                signal_info=signal_info
            )

            fixed = clean_assertion(fix_result.fixed_assertion)

            # Validate the fix
            is_valid, errors = validator.validate_assertion(fixed)
            if is_valid:
                refined = fixed
                break

        # Revert to original if still invalid
        if not is_valid:
            refined = assertion_clean
```

## Validation Flow Example

### Input (from Stage 2):
```systemverilog
as__reset_full: assert property (@(posedge clk) $rose(rst_n) |=> !full);
```

### After Refinement (LLM):
```systemverilog
assert property (as__reset_full @(posedge clk) $rose(DUT.rst_n) |=> !DUT.full);
```

### Verilator Validation:
```
✗ Syntax errors detected (1 errors)
  - [Error] Line 38: syntax error, unexpected IDENTIFIER, expecting ')'
```

### Feedback to LLM:
```
Original: assert property (as__reset_full @(posedge clk) $rose(DUT.rst_n) |=> !DUT.full);
Errors:
  - [Error] Line 38: syntax error, unexpected IDENTIFIER, expecting ')'

Fix the syntax while preserving logic.
```

### After Syntax Fix:
```systemverilog
as__reset_full: assert property (@(posedge clk) $rose(DUT.rst_n) |=> !DUT.full);
```

### Verilator Re-validation:
```
✓ Syntax validation passed
```

## Verilator Configuration

The validator runs with these flags:

- `--lint-only`: Syntax checking only, no compilation
- `--timing`: Enable SystemVerilog timing constructs (delays, assertions)
- `-Wno-DECLFILENAME`: Suppress filename mismatch warnings
- `-Wno-UNUSEDSIGNAL`: Suppress unused signal warnings in test wrapper
- `-Wno-UNUSEDPARAM`: Suppress unused parameter warnings
- `-Wno-UNDRIVEN`: Suppress undriven signal warnings

This configuration focuses on assertion syntax errors while ignoring test harness artifacts.

## Enhanced Assertion Refinement Signature

Updated the refinement signature with explicit warnings:

```python
class AssertionRefinement(dspy.Signature):
    """
    CRITICAL - DO NOT generate malformed assertions:
    - NEVER put the label inside assert property()
      WRONG: "assert property (label: @(posedge clk)...)"
    - CORRECT label placement: "label: assert property (@(posedge clk)...)"
    - Examples of CORRECT assertions:
      * as__test: assert property (@(posedge clk) wr_en && !full |=> wr_ack);
      * as__full: assert property (@(posedge clk) count == DEPTH |-> full);
    """
```

## Benefits

1. **Catches Real Syntax Errors**: Verilator finds errors that regex patterns can't detect
2. **Automated Fixes**: Feedback loop attempts to automatically correct syntax errors
3. **Preserves Logic**: Syntax fixer only changes syntax, not assertion logic/signals
4. **Graceful Fallback**: Reverts to original if fixes fail after 2 attempts
5. **Multi-Stage Validation**:
   - Pattern validation (malformed structures)
   - Pre-signal-update syntax validation
   - Post-signal-update syntax validation

## Testing

### Valid Assertions (Pass):
```systemverilog
✓ as__test1: assert property (@(posedge clk) wr_en |=> wr_ack);
✓ as__test2: assert property (@(posedge clk) $rose(rst_n) |=> !full);
```

### Invalid Assertions (Caught):
```systemverilog
✗ property assert (@(posedge clk) ...);  // Wrong order
✗ assert property (label: @(posedge clk) ...);  // Label inside
✗ assert property (@(posedge clk) wr_en |-> ##7);  // Incomplete
```

## Files Modified

### New Files:
1. **`sv_validator.py`** - Verilator-based syntax validator
2. **`SYNTAX_VALIDATION_FEEDBACK.md`** - This documentation

### Modified Files:
1. **`stage3.py`**:
   - Added `AssertionSyntaxFix` signature (lines 40-59)
   - Enhanced `AssertionRefinement` signature with label placement warnings
   - Integrated validator initialization (lines 607-616)
   - Added syntax validation feedback loop (lines 675-739)

2. **`.gitignore`**:
   - Added documentation files to ignore list

## Usage

The validator runs automatically in Stage 3:

```bash
# Run Stage 3 with validation
uv run main.py --stage 3

# Output shows validation progress:
✓ SystemVerilog validator initialized (Verilator)
================================================================================
REFINING ASSERTIONS WITH SYNTAX VALIDATION
================================================================================

[1/11] Original assertion:
  as__test: assert property (@(posedge clk) wr_en |=> wr_ack);
  Refined: as__test: assert property (@(posedge clk) DUT.wr_en |=> DUT.wr_ack);
  ✓ Syntax validation passed
  Updated signal references
  ✓ Saved to progress file
```

If validation fails:
```
[2/11] Original assertion:
  ✗ Syntax errors detected (1 errors)
      - [Error] Line 38: syntax error...
  🔧 Attempting syntax fix (attempt 1/2)...
  ✓ Syntax fixed successfully!
  Updated signal references
  ✓ Saved to progress file
```

## Impact

With syntax validation and feedback loop:
- ✅ Verilator validates all assertions before final output
- ✅ Syntax errors caught and reported with line numbers
- ✅ Automated fix attempts with error-specific feedback
- ✅ Label placement errors automatically corrected
- ✅ Multi-stage validation (pre and post signal updates)
- ✅ Graceful fallback to original if fixes fail
- ✅ Clear progress reporting during refinement

The pipeline now produces **syntactically correct** assertions validated by Verilator, the industry-standard SystemVerilog linter.
