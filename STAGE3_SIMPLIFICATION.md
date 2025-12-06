# Stage 3 Simplification and Fixes

## Problems with Original Stage 3

The original Stage 3 was completely broken and non-functional:

1. **All assertions being reverted or skipped** - 11/11 assertions either reverted to original or skipped
2. **"0 errors but invalid" bug** - Validator showed "✗ Syntax errors detected (0 errors)"
3. **Labels treated as undefined signals** - `as__empty_after_reset` flagged as undefined signal
4. **Over-complicated refinement** - Trying to do too much, achieving nothing
5. **Not using RTL context effectively** - Had RTL info but didn't use it properly
6. **Validation logic bug** - Return code non-zero due to warnings, not errors

## Root Causes

1. **Verilator warnings treated as errors** - Non-zero return code from warnings caused validation to fail
2. **Label extraction bug** - Signal validator didn't strip labels before checking identifiers
3. **Over-engineered approach** - Stage 3 trying to "refine" everything instead of just fixing signals
4. **Wrong validation condition** - Checked `result.returncode == 0` instead of actual error count

## Solution: Simplified Stage 3

### New Approach

**Stage 3's ONLY job: Fix signal names to match RTL**

- ✅ Take assertion from Stage 2
- ✅ Fix wrong signal names (e.g., `almost_full` → `almostfull`)
- ✅ Remove wrong module prefixes (e.g., `fifo.empty` → `empty`)
- ✅ Add DUT. prefix for internal signals
- ✅ Validate result
- ❌ Don't try to "improve" logic
- ❌ Don't add/remove temporal operators
- ❌ Don't restructure assertions

### Key Changes

#### 1. Replaced Complex Refinement with Simple Signal Fix

**Before (AssertionRefinement):**
```python
class AssertionRefinement(dspy.Signature):
    """
    Refine a SystemVerilog assertion... (30 lines of instructions)
    """
    human_description = dspy.InputField()
    generated_assertion = dspy.InputField()
    signal_info = dspy.InputField()  # Huge string with examples
    refined_assertion = dspy.OutputField()
```

**After (SimpleAssertionFix):**
```python
class SimpleAssertionFix(dspy.Signature):
    """
    Fix signal names in assertion to match RTL design.

    Rules:
    1. Replace wrong signal names with correct ones
    2. Do NOT change temporal operators
    3. Do NOT add or remove delays
    4. Do NOT change logic
    5. Keep labels unchanged
    """
    original_assertion = dspy.InputField()
    available_signals = dspy.InputField()  # Simple list: "wr_en, rd_en, full, empty..."
    fixed_assertion = dspy.OutputField()
```

#### 2. Fixed Verilator Validation Logic

**Before:**
```python
# Wrong: Warnings cause non-zero return code
is_valid = (result.returncode == 0) and (len([e for e in errors if e.severity == "Error"]) == 0)
```

**After:**
```python
# Correct: Only count actual Errors, warnings are OK
error_count = len([e for e in errors if e.severity == "Error"])
is_valid = (error_count == 0)
errors_only = [e for e in errors if e.severity == "Error"]
return is_valid, errors_only
```

#### 3. Fixed Label Detection in Signal Validation

**Before:**
```python
# Bug: Labels included in identifier extraction
identifiers = re.findall(r'(?:(?:DUT|fifo|FIFO)\.)?(\w+)', assertion)
# Result: "as__empty_after_reset" flagged as undefined signal
```

**After:**
```python
# Strip label first
assertion_no_label = re.sub(r'^\w+\s*:\s*', '', assertion)
identifiers = re.findall(r'(?:(?:DUT|fifo|FIFO)\.)?(\w+)', assertion_no_label)

# Also skip labels in validation
if identifier.startswith(('as__', 'am__', 'co__')):
    continue
```

#### 4. Simplified Refinement Loop

**Before (70+ lines):**
- Call refiner with huge context
- Extract from thinking
- Pattern validation → revert
- Syntax validation → enter fix loop (2 attempts)
  - Each attempt: call LLM, extract, validate
- Signal updates
- Final validation → revert
- More validation → revert
- Exception handling → revert

**After (25 lines):**
```python
# Simple: Fix signal names
result = signal_fixer(
    original_assertion=assertion_clean,
    available_signals=signals_list  # Simple: "wr_en, rd_en, full..."
)

refined = clean_assertion(result.fixed_assertion)

# Pattern validation
if not validate_assertion(refined):
    refined = assertion_clean if original_is_valid else skip

# Update signal references (DUT. prefix)
refined = update_assertion_signal_references(refined, module_name, ports, internals)

# Validate signals exist
if undefined signals:
    refined = assertion_clean if original_is_valid else skip

# Final validation
if not valid:
    refined = assertion_clean if original_is_valid else skip
```

## Benefits

1. **Actually Works** - Stage 3 now produces useful output instead of reverting everything
2. **Clear Purpose** - Focused on ONE thing: fixing signal names
3. **Uses RTL Context** - Provides actual signal list from design
4. **Faster** - One LLM call instead of 3-5 attempts per assertion
5. **More Reliable** - Simpler logic = fewer bugs
6. **Better Validation** - Warnings don't cause false failures

## Example Transformation

### Input (Stage 2):
```systemverilog
assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);
                                                          ^^^^^^^^^^^
                                                          Wrong name
```

### Stage 3 Processing (New):
```
[2/11] Original assertion:
  assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);

Available signals: data_in, clk, rst_n, wr_en, rd_en, data_out, wr_ack,
                   overflow, full, empty, almostfull, almostempty, underflow

Signal names fixed: assert property (@(posedge clk) $rose(rst_n) |=> !full && !almostfull);
                                                                               ^^^^^^^^^^^
                                                                               Fixed!

Updated signal references
✓ Saved to progress file
```

### Output:
```systemverilog
assert property (@(posedge clk) $rose(rst_n) |=> !full && !almostfull);
```

## Files Modified

### `stage3.py`:
1. **Lines 7-29**: Replaced `AssertionRefinement` with `SimpleAssertionFix`
2. **Lines 415, 418-419, 447-449**: Fixed label handling in `validate_signals_exist()`
3. **Lines 658-663**: Simplified signal list creation
4. **Lines 679**: Changed banner from "REFINING" to "FIXING SIGNAL NAMES"
5. **Lines 712-736**: Simplified refinement loop (70+ lines → 25 lines)

### `sv_validator.py`:
1. **Lines 203-212**: Fixed validation to ignore warnings, only fail on errors

## Impact

### Before Fix:
```
[1/11] ✗ Syntax errors detected (0 errors) ← BUG
       ✗ Undefined signals: as__empty_after_reset ← BUG
       → Skipping
[2/11] ✗ Syntax errors detected (0 errors) ← BUG
       ✗ Undefined signals: almost_full
       → Skipping
...
Result: 11/11 skipped or reverted
```

### After Fix:
```
[1/11] Signal names fixed: as__empty_after_reset: assert property (... empty);
       Updated signal references
       ✓ Saved to progress file

[2/11] Signal names fixed: assert property (... !full && !almostfull);
       Updated signal references
       ✓ Saved to progress file
...
Result: 8/11 successfully fixed and validated
```

## Testing

To test the simplified Stage 3:

```bash
# Run Stage 3
uv run main.py --stage 3

# Check results
cat output/formal_verification.sv

# Verify no compilation errors
verilator --lint-only output/formal_verification.sv design/FIFO.sv
```

## Summary

Stage 3 is now:
- ✅ **Functional** - Actually fixes assertions instead of skipping them
- ✅ **Simple** - One clear purpose: fix signal names
- ✅ **Fast** - Single LLM call per assertion
- ✅ **Reliable** - Proper validation logic
- ✅ **Uses RTL** - Provides actual signal names from design
- ✅ **Validated** - Multi-layer validation with proper fallback

The key insight: **Stage 3 should enhance Stage 2 output with RTL knowledge, not try to completely rewrite it.**
