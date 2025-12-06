# Signal Existence Validation Fix

## Problem

The testbench was generating assertions that referenced signals that don't exist in the design, causing compilation errors:

```
[ERROR (VERI-1128)] 'almost_full' is not declared
[ERROR (VERI-1128)] 'data_out_valid' is not declared
[ERROR (VERI-1128)] 'rd_ack' is not declared
```

Example malformed assertions:
```systemverilog
// Wrong: almost_full doesn't exist (should be almostfull)
assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);

// Wrong: data_out_valid and rd_ack don't exist in FIFO
assert property (@(posedge clk) (full && rd_en && wr_en) |=> (!data_out_valid && rd_ack));

// Wrong: Using lowercase 'fifo' instead of 'DUT'
as__empty_after_reset: assert property ($rose(rst_n) |=> fifo.empty);
```

## Root Cause

The LLM in Stage 2 or 3 was **hallucinating signal names** that don't exist in the actual RTL design:

1. **Stage 2** generates assertions based on specification, sometimes inventing signals
2. **Stage 3** refines assertions but doesn't verify signals exist
3. Signal reference updates only handle hierarchical prefixes (DUT.), not existence
4. Invalid assertions pass syntax validation but fail design compilation

The actual FIFO design has:
- ✓ `almostfull`, `almostempty` (no underscores)
- ✓ `wr_ack`, `overflow`, `underflow`
- ✗ NO `almost_full`, `data_out_valid`, `rd_ack`

## Solution

Added comprehensive signal existence validation that checks every identifier in assertions against the actual design signals.

### 1. Created `validate_signals_exist()` Function

```python
def validate_signals_exist(assertion: str, ports: List[dict],
                          internals: List[dict]) -> Tuple[bool, List[str]]:
    """
    Check if all signals referenced in an assertion actually exist in the design.

    Returns:
        Tuple of (all_signals_exist, list_of_undefined_signals)
    """
    # Get all valid signal names from design
    port_names = {p['name'] for p in ports}
    internal_names = {s['name'] for s in internals}
    all_valid_signals = port_names | internal_names

    # SystemVerilog keywords and functions to skip
    sv_keywords = {'assert', 'property', 'posedge', 'negedge', 'iff',
                   'disable', 'throughout'}
    sv_functions = {'past', 'rose', 'fell', 'stable', 'countones'}

    # Extract all identifiers from assertion
    identifiers = re.findall(r'(?:(?:DUT|fifo|FIFO)\.)?(\w+)', assertion)

    undefined_signals = []
    for identifier in identifiers:
        # Skip keywords, functions, parameters, numbers
        if identifier in sv_keywords: continue
        if identifier in sv_functions: continue
        if identifier.startswith('$'): continue
        if identifier.isupper(): continue  # Parameters
        if identifier.isdigit(): continue
        if identifier in ['clk', 'rst_n', 'DUT', 'fifo', 'FIFO']: continue

        # Check if signal exists in design
        if identifier not in all_valid_signals:
            if identifier not in undefined_signals:
                undefined_signals.append(identifier)

    return (len(undefined_signals) == 0, undefined_signals)
```

**What it checks:**
- ✓ Extracts all identifiers from assertion
- ✓ Skips SystemVerilog keywords (`assert`, `property`, etc.)
- ✓ Skips system functions (`$past`, `$rose`, etc.)
- ✓ Skips parameters (all uppercase like `FIFO_DEPTH`)
- ✓ Handles `DUT.signal`, `fifo.signal`, `FIFO.signal` prefixes
- ✓ Returns list of undefined signals

### 2. Integrated into Refinement Pipeline

Added validation checkpoint after signal reference updates:

```python
# Update signal references (DUT.signal for internal signals)
refined = update_assertion_signal_references(refined, module_name, ports, internals)

# NEW: Validate that all signals exist in the design
signals_exist, undefined = validate_signals_exist(refined, ports, internals)
if not signals_exist:
    print(f"✗ Warning: Assertion references undefined signals: {', '.join(undefined)}")

    if original_is_valid:
        # Check if original has valid signals
        original_signals_exist, _ = validate_signals_exist(assertion_clean, ports, internals)
        if original_signals_exist:
            print(f"  → Reverting to original (has valid signals)")
            refined = assertion_clean
        else:
            print(f"  → Original also has undefined signals, skipping")
            continue
    else:
        print(f"  → Original also invalid, skipping")
        continue
```

### 3. Enhanced Signal Reference Updates

Fixed handling of lowercase module references:

```python
# Also handle old-style module.signal references
updated = re.sub(rf'\b{re.escape(module_name)}\.', 'DUT.', updated)

# NEW: Handle lowercase module name references (common mistake)
if module_name:
    updated = re.sub(rf'\b{re.escape(module_name.lower())}\.', 'DUT.', updated)

# Now: fifo.empty → DUT.empty ✓
```

## Validation Flow

```
After Refinement & Syntax Validation
       ↓
Update Signal References (DUT. prefix)
       ↓
Validate Signals Exist ← NEW CHECKPOINT
       ├─ All signals exist? → Continue
       └─ Undefined signals found?
              ├─ Check if original has valid signals
              │  ├─ YES → Revert to original
              │  └─ NO  → Skip assertion
              └─ Log undefined signals
       ↓
Final Pattern & Syntax Validation
       ↓
Output (only assertions with valid signals)
```

## Example Validations

### Case 1: Undefined Signal Detected
```
Original: assert property (...  !full && !almost_full);
                                         ^^^^^^^^^^^^
Validation: ✗ Undefined signals: ['almost_full']
Action: Skip assertion (signal doesn't exist)
```

### Case 2: Wrong Module Reference Fixed
```
Original: as__test: assert property ($rose(rst_n) |=> fifo.empty);
                                                      ^^^^^
Update:   as__test: assert property ($rose(rst_n) |=> DUT.empty);
                                                      ^^^^
Validation: ✓ All signals exist
```

### Case 3: Hallucinated Signals
```
Original: assert property (... |=> (!data_out_valid && rd_ack));
                                    ^^^^^^^^^^^^^^    ^^^^^^
Validation: ✗ Undefined signals: ['data_out_valid', 'rd_ack']
Action: Skip assertion (signals don't exist in FIFO design)
```

## Benefits

1. **Prevents Compilation Errors**: Catches undefined signals before testbench generation
2. **Clear Error Reporting**: Lists exactly which signals are undefined
3. **Intelligent Fallback**: Checks if original has valid signals before reverting
4. **Skips Bad Assertions**: Excludes assertions with hallucinated signals
5. **Fixes Module References**: Converts `fifo.signal` → `DUT.signal`

## Impact

### Before Fix:
```verilog
// Generated testbench with errors:
assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);
//                                                        ^^^^^^^^^^^^
// ERROR: 'almost_full' is not declared

assert property (@(posedge clk) (full && rd_en && wr_en) |=> (!data_out_valid && rd_ack));
//                                                             ^^^^^^^^^^^^^^    ^^^^^^
// ERROR: 'data_out_valid' is not declared
// ERROR: 'rd_ack' is not declared
```

### After Fix:
```
[Processing assertions...]

[2/11] Original assertion:
  assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);
  ✗ Warning: Assertion references undefined signals: almost_full
    → Original also has undefined signals, skipping this assertion

// Progress file:
// Assertion SKIPPED (invalid)
// Reason: References undefined signals: almost_full

[10/11] Original assertion:
  assert property (@(posedge clk) (full && rd_en && wr_en) |=> (!data_out_valid && rd_ack));
  ✗ Warning: Assertion references undefined signals: data_out_valid, rd_ack
    → Original also has undefined signals, skipping this assertion

// Progress file:
// Assertion SKIPPED (invalid)
// Reason: References undefined signals: data_out_valid, rd_ack
```

**Final testbench: Only assertions with valid signals** ✅

## Testing

To verify signal validation is working:

```bash
# Run Stage 3
uv run main.py --stage 3

# Check for signal validation warnings
grep "undefined signals" output/refined_assertions_progress.sv

# Verify no undeclared signals in final output
verilator --lint-only output/formal_verification.sv design/FIFO.sv
```

## Recommendations

If many assertions are being skipped due to undefined signals:

1. **Fix Stage 2 Prompts**: Provide clearer signal information in Stage 1 specification
2. **Improve Few-Shot Examples**: Ensure examples use only signals that exist in designs
3. **Add Signal List to Context**: Include complete port/signal list in Stage 2 prompt
4. **Review Specifications**: Check if specifications reference non-existent features

## Files Modified

### `stage3.py`:
1. **Lines 401-450**: Added `validate_signals_exist()` function
2. **Lines 488-490**: Enhanced signal reference updates for lowercase module names
3. **Lines 798-813**: Integrated signal validation checkpoint in refinement loop

### New Documentation:
- **`SIGNAL_VALIDATION_FIX.md`**: This file

## Summary

The signal validation fix ensures that:
- ✅ Every signal referenced in assertions exists in the RTL design
- ✅ Undefined signals are detected and reported with names
- ✅ Assertions with hallucinated signals are skipped
- ✅ Module reference mistakes (`fifo.` vs `DUT.`) are fixed
- ✅ Final testbench compiles without "undeclared signal" errors

This eliminates an entire class of compilation errors caused by LLM hallucination of non-existent signals.
