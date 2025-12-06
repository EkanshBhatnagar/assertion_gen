# Validation Fallback Fix - Never Output Invalid Assertions

## Problem

Malformed assertions like this were appearing in final output:

```systemverilog
assert property (@(posedge clk)
    (DUT.wr_en && !DUT.full) |-> ##7);
```

This assertion has `|-> ##7);` which is invalid (implication to delay with no consequent).

## Root Cause

The issue was in the fallback logic during Stage 3 refinement:

### Original Flawed Logic:
```python
# If refinement produces invalid assertion
if not validate_assertion(refined):
    print("Warning: Assertion failed validation, using original")
    refined = assertion_clean  # ← BUG: What if original is ALSO invalid?
```

**The Problem:**
1. Stage 2 generates assertion (might be invalid)
2. Stage 3 refines it (might still be invalid)
3. Validation fails
4. Code reverts to original from Stage 2
5. **Original is never validated** → invalid assertion reaches output!

### Flow Diagram (Before Fix):

```
Stage 2 Output (possibly invalid)
       ↓
Stage 3 Refinement
       ↓
Validation FAIL
       ↓
Revert to original ← NO VALIDATION OF ORIGINAL!
       ↓
Invalid assertion in output ❌
```

## Solution

Added validation of the original assertion at the start, and changed ALL fallback points to check if the original is valid before using it.

### New Logic:

```python
# At the start of processing each assertion
original_is_valid = validate_assertion(assertion_clean)
if not original_is_valid:
    print("⚠ Warning: Original from Stage 2 is malformed - will attempt to fix")

# At every fallback point
if not validate_assertion(refined):
    print("✗ Warning: Assertion failed validation")
    if original_is_valid:
        print("  → Reverting to original (valid)")
        refined = assertion_clean
    else:
        print("  → Original also invalid, skipping this assertion")
        continue  # Skip this assertion entirely!
```

### New Flow Diagram (After Fix):

```
Stage 2 Output
       ↓
Validate Original → Store: original_is_valid
       ↓
Stage 3 Refinement
       ↓
Validation FAIL
       ↓
Check: is original_is_valid?
       ├─ YES → Revert to original ✓
       └─ NO  → Skip assertion (better than outputting invalid) ✓
       ↓
Only valid assertions in output ✅
```

## Implementation Details

### 1. Validate Original at Start

```python
for i, assertion in enumerate(assertions, 1):
    assertion_clean = clean_assertion(assertion)

    # Validate the original assertion from Stage 2
    original_is_valid = validate_assertion(assertion_clean)
    if not original_is_valid:
        print(f"  ⚠ Warning: Original from Stage 2 is malformed - will attempt to fix")
```

### 2. Updated ALL Fallback Points

**Fallback Point 1: Empty/Short Extraction**
```python
if not refined or len(refined) < 10:
    if original_is_valid:
        refined = assertion_clean
    else:
        continue  # Skip assertion
```

**Fallback Point 2: Pattern Validation Failure**
```python
if not validate_assertion(refined):
    if original_is_valid:
        refined = assertion_clean
    else:
        continue  # Skip assertion
```

**Fallback Point 3: Syntax Fix Failure**
```python
if not is_valid:  # After syntax fix attempts
    if original_is_valid:
        refined = assertion_clean
    else:
        continue  # Skip assertion
```

**Fallback Point 4: Signal Update Validation**
```python
if not validate_assertion(refined):  # After signal updates
    if original_is_valid:
        refined = assertion_clean
    else:
        continue  # Skip assertion
```

**Fallback Point 5: Final Syntax Check**
```python
if not is_valid_final:  # After signal updates
    if original_is_valid:
        refined = assertion_clean
    else:
        continue  # Skip assertion
```

**Fallback Point 6: Exception Handling**
```python
except Exception as e:
    if original_is_valid:
        refined_assertions.append(assertion_clean)
    else:
        # Log as skipped in progress file
        continue
```

### 3. Track Skipped Assertions

When an assertion is skipped, it's documented in the progress file:

```python
with open(progress_file, "a") as f:
    f.write(f"// Assertion SKIPPED (invalid)\n")
    f.write(f"// Human description: {human_desc}\n")
    f.write(f"// Original: {assertion_clean}\n")
    f.write(f"// Reason: Both original and refined assertions failed validation\n\n")
```

## Example Scenarios

### Scenario 1: Both Valid
```
Original from Stage 2: VALID
Refinement: VALID
→ Output: Refined (with signal updates)
```

### Scenario 2: Refinement Fails, Original Valid
```
Original from Stage 2: VALID
Refinement: INVALID
→ Output: Original (fallback to valid version)
```

### Scenario 3: Both Invalid (NEW BEHAVIOR)
```
Original from Stage 2: INVALID (e.g., "|-> ##7);")
Refinement: INVALID
→ Output: SKIPPED (nothing - better than invalid)
```

### Scenario 4: Original Invalid, Refinement Valid (BEST CASE)
```
Original from Stage 2: INVALID
Refinement: VALID (fixed by LLM or syntax fix loop)
→ Output: Refined (successfully fixed)
```

## Benefits

1. **Guaranteed Valid Output**: No invalid assertions can reach final testbench
2. **Clear Reporting**: Warns when original is malformed
3. **Skipped Assertions Logged**: Progress file documents why assertions were skipped
4. **Multiple Safety Nets**: 6 validation checkpoints all respect original validity
5. **Encourages Stage 2 Quality**: Incentivizes fixing Stage 2 to produce valid assertions

## Testing

### Test Case: Malformed Original

**Input (Stage 2):**
```systemverilog
assert property (@(posedge clk) (wr_en && !full) |-> ##7);
```

**Stage 3 Processing:**
```
[1/1] Original assertion:
  assert property (@(posedge clk) (wr_en && !full) |-> ##7);
  ⚠ Warning: Original from Stage 2 is malformed - will attempt to fix
  Human description: Write acknowledgement after write

  Refined: ...
  ✗ Warning: Assertion failed pattern validation (malformed)
    → Original also invalid, skipping this assertion

// Progress file entry:
// Assertion SKIPPED (invalid)
// Human description: Write acknowledgement after write
// Original: assert property (@(posedge clk) (wr_en && !full) |-> ##7);
// Reason: Both original and refined assertions failed validation
```

**Final Output:**
- Assertion not included in testbench
- User sees clear warning
- Progress file explains why it was skipped

## Files Modified

### `stage3.py` Changes:

1. **Lines 645-648**: Added original assertion validation
   ```python
   original_is_valid = validate_assertion(assertion_clean)
   ```

2. **Lines 669-688**: Updated empty/short extraction fallback
3. **Lines 681-688**: Updated pattern validation fallback
4. **Lines 733-741**: Updated syntax fix failure fallback
5. **Lines 750-757**: Updated signal update validation fallback
6. **Lines 762-769**: Updated final syntax check fallback
7. **Lines 784-802**: Updated exception handling fallback

## Impact

With this fix:
- ✅ **Zero Invalid Assertions**: Impossible to output invalid assertions
- ✅ **Clear Warnings**: User knows when assertions are skipped
- ✅ **Documented Skips**: Progress file explains each skipped assertion
- ✅ **No Silent Failures**: Every assertion accounted for (output or logged skip)
- ✅ **Better Stage 2 Feedback**: Identifies when Stage 2 produces malformed output

## Recommendations

If assertions are frequently being skipped:

1. **Improve Stage 2**: Fix the prompt/examples to generate valid assertions
2. **Check Examples**: Ensure few-shot examples in `examples/` are all valid
3. **Review Specifications**: Stage 1 descriptions might be confusing Stage 2
4. **Adjust Temperature**: Lower temperature in Stage 2 for more conservative output

The validation feedback loop will attempt to fix invalid assertions, but it's better if Stage 2 produces valid output from the start.
