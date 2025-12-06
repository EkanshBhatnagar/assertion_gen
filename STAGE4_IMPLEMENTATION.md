# Stage 4 Implementation Summary

## Overview
Added Stage 4 to the assertion generation pipeline, which generates JasperGold TCL scripts for formal verification. Also implemented a comprehensive configuration system and unified pipeline orchestration.

## New Files

### 1. `stage4.py`
Generates JasperGold TCL scripts for formal verification.

**Features:**
- Uses few-shot learning with 4 TCL examples from `examples/*/FPV.tcl`
- DSPy signature: `JasperGoldTCLGeneration`
- Local LM Studio model for generation
- Fallback to template-based generation if LLM fails
- Generates:
  - analyze commands for RTL and testbench
  - elaborate command with top module
  - clock and reset setup
  - proof configuration settings
  - autoprove command
  - report generation

### 2. `config.py`
Centralized configuration management.

**Features:**
- Configurable RTL file paths and top module name
- Clock and reset signal configuration (active high/low)
- Output directory management
- API key management
- Model selection for each stage
- JasperGold proof settings

**Key Methods:**
- `set_design(rtl_file, top_module, spec_file)` - Configure design files
- `set_clock_reset(clock, reset, active_low)` - Configure signals
- `get_reset_expression()` - Get JasperGold reset expression

### 3. New `main.py`
Complete pipeline orchestration with CLI.

**Features:**
- Run all stages or individual stages
- Command-line arguments for custom configurations
- Progress tracking and error handling
- Comprehensive help and examples

**Usage:**
```bash
# Run all stages
uv run main.py --all

# Run specific stages
uv run main.py --stage 2 3 4

# Custom configuration
uv run main.py --all \
  --rtl design/UART.sv \
  --top UART \
  --spec design/uart_spec.md \
  --clock sys_clk \
  --reset sys_rst
```

## Enhanced Files

### `example_loader.py`
Added TCL example loading functionality:
- `load_tcl_examples()` - Load FPV.tcl files from examples
- `create_tcl_few_shot_prompt()` - Format TCL examples for DSPy

### `.gitignore`
Added:
- Old/backup file patterns
- IDE-specific files (VSCode, IntelliJ)
- OS-specific files (macOS, Windows)

## Pipeline Architecture

```
┌──────────────────────────────────────────────────────────────┐
│                     CONFIGURATION                            │
│                      (config.py)                             │
│  - RTL paths, top module                                     │
│  - Clock/reset signals                                       │
│  - Model selection                                           │
└──────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌──────────────────────────────────────────────────────────────┐
│                    STAGE 1: Spec → Prompts                   │
│  Model: Claude-3-Opus (OpenRouter)                          │
│  Input:  design/specification.md                            │
│  Output: output/assertion_prompts.txt                       │
└──────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌──────────────────────────────────────────────────────────────┐
│              STAGE 2: Prompts → SVA (Few-Shot)               │
│  Model: Claude-3-Opus (OpenRouter)                          │
│  Examples: 8 high-quality SVA examples                      │
│  Input:  output/assertion_prompts.txt                       │
│  Output: output/generated_assertions.sv                     │
└──────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌──────────────────────────────────────────────────────────────┐
│            STAGE 3: SVA → Testbench (Few-Shot)               │
│  Model: Local LM Studio (gpt-oss-20b)                       │
│  Examples: 10 quality SVA examples                          │
│  Input:  output/generated_assertions.sv + design/FIFO.sv    │
│  Output: output/formal_verification.sv (testbench)          │
│         output/refined_assertions_progress.sv                │
└──────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌──────────────────────────────────────────────────────────────┐
│           STAGE 4: Generate TCL Script (Few-Shot)            │
│  Model: Local LM Studio (gpt-oss-20b)                       │
│  Examples: 4 JasperGold TCL examples                        │
│  Input:  output/formal_verification.sv + design/FIFO.sv     │
│  Output: output/jaspergold_fpv.tcl                          │
└──────────────────────────────────────────────────────────────┘
                              │
                              ▼
                    ┌──────────────────┐
                    │  JasperGold FPV  │
                    │  Verification    │
                    └──────────────────┘
```

## Configuration Examples

### Default Configuration
```python
config = Config()
# RTL: design/FIFO.sv
# Top: FIFO
# Clock: clk
# Reset: rst_n (active low)
```

### Custom Configuration
```python
config.set_design(
    rtl_file="design/UART.sv",
    top_module="UART",
    spec_file="design/uart_spec.md"
)
config.set_clock_reset(
    clock="sys_clk",
    reset="sys_rst",
    reset_active_low=False
)
```

### Via Command Line
```bash
uv run main.py --all \
  --rtl design/UART.sv \
  --top UART \
  --spec design/uart_spec.md \
  --clock sys_clk \
  --reset sys_rst \
  --reset-active-high
```

## Testing

All components tested and working:

```bash
# Test configuration
uv run config.py
# ✓ Loads default configuration correctly

# Test example loader
uv run example_loader.py
# ✓ Loads 228 SVA examples
# ✓ Loads 4 TCL examples

# Test help system
uv run main.py --help
# ✓ Shows comprehensive help

# Test stage 4 standalone
uv run stage4.py
# ✓ Generates TCL script with template fallback
```

## Output Files

After running all stages:

```
output/
├── assertion_prompts.txt              # Stage 1 output
├── generated_assertions.sv            # Stage 2 output
├── formal_verification.sv             # Stage 3 output (testbench)
├── refined_assertions_progress.sv     # Stage 3 progress
└── jaspergold_fpv.tcl                 # Stage 4 output (NEW!)
```

## Running Formal Verification

After generating all files:

```bash
# Option 1: Direct execution
jaspergold output/jaspergold_fpv.tcl

# Option 2: In JasperGold GUI
jaspergold
# Then in GUI: source output/jaspergold_fpv.tcl

# Option 3: Batch mode
jg -batch output/jaspergold_fpv.tcl
```

## Benefits

1. **Complete Automation**: Full pipeline from specification to runnable formal verification
2. **Flexible Configuration**: Easy to adapt for different designs
3. **Few-Shot Learning**: Uses high-quality examples at every stage
4. **Fallback Mechanisms**: Template generation if LLM fails
5. **Proper Testbench**: No $root references, proper DUT instantiation
6. **Tool-Ready Output**: TCL script ready for JasperGold

## Future Enhancements

Potential improvements:
- Support for multiple clock domains
- Automatic clock/reset detection from RTL
- Support for other formal tools (Cadence, Synopsys)
- Parallel stage execution where possible
- Results parsing and reporting
- Interactive mode for iterative refinement
