# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a **multi-stage SystemVerilog Assertion (SVA) generation pipeline** that uses LLMs to generate formal verification code from hardware design specifications. The project specifically targets a Synchronous FIFO design.

### Four-Stage Pipeline Architecture

1. **Stage 1 (stage1.py)**: Specification → Assertion Prompts
   - Input: Hardware specification (Markdown)
   - Output: Human-language assertion prompts (`output/assertion_prompts.txt`)
   - Model: OpenRouter/Claude-3-Opus via DSPy
   - Uses `SpecificationToPrompts` signature to generate natural language descriptions

2. **Stage 2 (stage2.py)**: Assertion Prompts → SystemVerilog Assertions
   - Input: Plain English assertion prompts from Stage 1
   - Output: Initial SystemVerilog assertions (`output/generated_assertions.sv`)
   - Model: OpenRouter/Claude-3-Opus via DSPy
   - **Uses few-shot learning** with 8 examples from `examples/` directory
   - Uses `EnglishAssertionToSystemVerilog` signature with detailed guidelines
   - Examples include high-quality assertions from FIFO, MMU, TLB, and PTW modules

3. **Stage 3 (stage3.py)**: Assertions + RTL → Formal Verification Testbench
   - Input: Generated assertions + RTL design code
   - Output: Complete testbench with DUT instantiation (`output/formal_verification.sv`)
   - Model: Local LM Studio (gpt-oss-20b) via DSPy
   - **Uses few-shot learning** with quality examples for refinement guidance
   - Performs signal matching, syntax correction, and testbench generation
   - **Generates testbench** (not bind statements) with:
     - All parameters copied from RTL
     - All ports declared as `logic`
     - DUT instantiation with proper port connections
     - Assertions with correct signal references (DUT.signal for internals)
   - Generates incremental progress file (`output/refined_assertions_progress.sv`)

4. **Stage 4 (stage4.py)**: Generate JasperGold TCL Script
   - Input: Testbench file, RTL file, configuration
   - Output: JasperGold TCL script (`output/jaspergold_fpv.tcl`)
   - Model: Local LM Studio (gpt-oss-20b) via DSPy
   - **Uses few-shot learning** with 4 TCL examples from `examples/`
   - Generates complete TCL script with:
     - analyze commands for RTL and testbench
     - elaborate command with top module
     - clock and reset setup
     - proof configuration settings
     - autoprove command
     - report generation

### Key Design Patterns

- **DSPy Framework**: All LLM interactions use DSPy signatures and modules (not raw prompts)
- **Few-Shot Learning**: Stages 2 and 3 use high-quality examples from `examples/` directory to improve assertion quality
- **Incremental Output**: Stage 3 writes progress after each assertion refinement to prevent data loss
- **Signal Extraction**: Stage 3 parses RTL to understand available signals and match them to assertions
- **Dual-Model Strategy**: Uses frontier models (Claude) for complex reasoning, local models for refinement

### Few-Shot Learning with Examples

The `examples/` directory contains 228 high-quality SystemVerilog assertions from 4 different modules:
- **ft_fifo**: 20 FIFO assertions
- **ft_mmu**: 22 MMU (Memory Management Unit) assertions
- **ft_tlb**: 68 TLB (Translation Lookaside Buffer) assertions
- **ft_ptw**: 118 PTW (Page Table Walker) assertions

These examples demonstrate:
- Proper assertion syntax and naming conventions (as__, am__, co__ prefixes)
- Temporal operators: `|->`, `|=>`, `##N`
- System functions: `$past`, `$stable`, `$countones`, `$rose`, `$fell`, `s_eventually`
- Generate blocks for parameterized assertions
- Hierarchical signal references

The `example_loader.py` module:
- Parses SVA files and extracts individual assertions
- Scores and ranks assertions by quality
- Converts examples to DSPy Example objects for few-shot prompting
- Used by both Stage 2 (generation) and Stage 3 (refinement)

## Running the Pipeline

### Prerequisites
```bash
# Ensure .env file contains:
OPENROUTER_API_KEY=<your-key>

# Ensure LM Studio is running on localhost:1234 for Stages 3 & 4
```

### Quick Start

```bash
# Run all stages at once
uv run main.py --all

# Or run with custom RTL file
uv run main.py --all --rtl design/UART.sv --top UART --spec design/uart_spec.md
```

### Running Individual Stages

```bash
# Stage 1: Generate assertion prompts from specification
uv run main.py --stage 1

# Stage 2: Generate SystemVerilog assertions from prompts
uv run main.py --stage 2

# Stage 3: Generate testbench with DUT instantiation
uv run main.py --stage 3

# Stage 4: Generate JasperGold TCL script
uv run main.py --stage 4

# Or run multiple stages
uv run main.py --stage 2 3 4
```

### Configuration

The pipeline uses `config.py` for configuration. Default settings:
- RTL file: `design/FIFO.sv`
- Specification: `design/specification.md`
- Top module: `FIFO` (extracted from RTL)
- Clock signal: `clk`
- Reset signal: `rst_n` (active low)

To override:
```bash
uv run main.py --all \
  --rtl design/MyModule.sv \
  --top MyModule \
  --spec design/my_spec.md \
  --clock sys_clk \
  --reset sys_rst \
  --reset-active-high
```

Each stage depends on outputs from the previous stage stored in `output/`.

## File Structure

```
design/
  ├── FIFO.sv              # RTL design module
  └── specification.md      # Hardware specification
examples/                   # Few-shot learning examples
  ├── ft_fifo/
  │   ├── sva/fifo_prop.sv # 20 FIFO assertions
  │   └── FPV.tcl          # JasperGold TCL script
  ├── ft_mmu/
  │   ├── sva/mmu_prop.sv  # 22 MMU assertions
  │   └── FPV.tcl
  ├── ft_tlb/
  │   ├── sva/tlb_prop.sv  # 68 TLB assertions
  │   └── FPV.tcl
  └── ft_ptw/
      ├── sva/ptw_prop.sv  # 118 PTW assertions
      └── FPV.tcl
output/                     # Generated files (created by pipeline)
  ├── assertion_prompts.txt
  ├── generated_assertions.sv
  ├── formal_verification.sv           # Testbench
  ├── refined_assertions_progress.sv   # Incremental progress
  └── jaspergold_fpv.tcl              # JasperGold script
config.py                   # Configuration (RTL paths, clock/reset, etc.)
example_loader.py           # Loads SVA and TCL examples
stage1.py                   # Stage 1: Spec → Prompts
stage2.py                   # Stage 2: Prompts → Assertions (uses examples)
stage3.py                   # Stage 3: Assertions → Testbench (uses examples)
stage4.py                   # Stage 4: Generate JasperGold TCL (uses examples)
main.py                     # Pipeline orchestration
```

## Working with the Codebase

### Adding Examples for Few-Shot Learning

To add new high-quality assertion examples:

1. Create a new subdirectory in `examples/` (e.g., `examples/ft_uart/`)
2. Create an `sva/` subdirectory
3. Add SystemVerilog property files ending with `_prop.sv`
4. Ensure assertions follow naming conventions:
   - `as__<name>` for assert properties
   - `am__<name>` for assume properties
   - `co__<name>` for cover properties
5. The example loader will automatically discover and use them

### Adding a New Design

To adapt this pipeline for a different hardware module:

1. Place RTL file in `design/` directory
2. Create corresponding `specification.md` in `design/`
3. Update hardcoded RTL path in `main.py:60` (currently `design/FIFO.sv`)
4. Run the three-stage pipeline

### Testbench Generation (Stage 3)

Stage 3 generates a complete testbench instead of using bind statements. This approach works better for formal verification tools.

**Signal Reference Rules:**
- **Port signals**: Referenced directly (e.g., `clk`, `rst_n`, `full`, `empty`)
- **Internal signals**: Referenced with DUT prefix (e.g., `DUT.count`, `DUT.wr_ptr`, `DUT.mem`)
- No `$root` references (not supported in formal verification)

**Testbench Structure:**
```systemverilog
module {module_name}_tb;
    // Parameters (copied from RTL)
    parameter FIFO_WIDTH = 16;
    parameter FIFO_DEPTH = 8;

    // Ports (all declared as logic)
    logic [FIFO_WIDTH-1:0] data_in;
    logic clk;
    logic rst_n;
    // ... more ports

    // DUT Instantiation
    FIFO #(
        .FIFO_WIDTH(FIFO_WIDTH),
        .FIFO_DEPTH(FIFO_DEPTH)
    ) DUT (
        .data_in(data_in),
        .clk(clk),
        // ... more connections
    );

    // Default clocking and reset
    default clocking cb @(posedge clk);
    endclocking
    default disable iff (!rst_n);

    // Assertions with correct signal references
    as__example: assert property (DUT.count == 0 |-> empty);
endmodule
```

### Modifying Stage 3 Behavior

Stage 3 contains the most complex logic:
- `extract_signal_info()`: Parses RTL to extract module name, parameters, ports (with widths), and internal signals
- `generate_testbench_code()`: Creates complete testbench with DUT instantiation
- `update_assertion_signal_references()`: Updates assertions to use DUT.signal for internal signals
- `extract_assertion_from_thinking()`: Extracts SV code from thinking model output
- `generate_formal_verification_code()`: Main orchestration function
- Uses DSPy signature: `AssertionRefinement` for assertion refinement with few-shot examples

### Stage 4: JasperGold TCL Generation

Stage 4 generates a TCL script for running formal verification with JasperGold:
- Uses few-shot learning with 4 TCL examples from `examples/*/FPV.tcl`
- Generates analyze commands for both RTL and testbench
- Sets up clock and reset signals
- Configures proof settings (time limit, proofgrid, etc.)
- If LLM generation fails, falls back to template-based generation

**Running the generated TCL:**
```bash
# After running all stages
jaspergold output/jaspergold_fpv.tcl

# Or in JasperGold GUI
jaspergold
# Then: source output/jaspergold_fpv.tcl
```

### Understanding DSPy Usage

All LLM calls use DSPy's declarative approach:
```python
class MySignature(dspy.Signature):
    """Docstring becomes system prompt"""
    input_field = dspy.InputField(desc="...")
    output_field = dspy.OutputField(desc="...")

class MyModule(dspy.Module):
    def __init__(self):
        self.predictor = dspy.ChainOfThought(MySignature)

    def forward(self, **kwargs):
        return self.predictor(**kwargs)
```

### LLM Configuration

- **Stage 1 & 2**: Configure OpenRouter in respective files (lines 28-37)
- **Stage 3**: Configures local LM Studio at `http://localhost:1234/v1` (line 178-186)
- All stages require API keys/endpoints to be accessible before running

### Output Files

- `assertion_prompts.txt`: Newline-separated prompts
- `generated_assertions.sv`: Raw assertions (may have signal mismatches)
- `refined_assertions_progress.sv`: Updated after each assertion in Stage 3 (for debugging)
- `formal_verification.sv`: Final output with assertion module + bind statement

## Temporal Operator Usage (CRITICAL)

### Understanding |-> vs |=>

The pipeline has been optimized to correctly use temporal operators:

**|-> (Same Cycle)**: Use for combinational logic
- Condition and consequence happen simultaneously
- Example: `count == DEPTH |-> full` (full is combinational)

**|=> (Next Cycle)**: Use for registered logic
- Consequence happens one clock cycle after condition
- Example: `wr_en && !full |=> wr_ack` (wr_ack is registered)

**Key Identification:**
- If signal is assigned in `always @(posedge clk)` with `<=` → Use |=>
- If signal is assigned with `assign` or `always @(*)` → Use |->

### Pipeline Improvements

**Stage 1:** Enhanced to specify timing in prompts
- Identifies registered vs combinational signals
- Adds "next cycle" or "same cycle" keywords to prompts

**Stage 2:** Enhanced with temporal operator guidance
- Detailed rules for choosing |-> vs |=>
- Prioritizes few-shot examples showing |=> usage (5 examples)
- Parses timing keywords from Stage 1 prompts

See `temporal_operators_guide.md` for comprehensive examples.

## Common Issues

- **Stage 2/3 missing input**: Run previous stages first; pipeline is strictly sequential
- **LM Studio connection error**: Ensure LM Studio server is running on port 1234 for Stages 3 & 4
- **Signal name mismatches**: Stage 3 should fix these, but complex designs may need manual regex tuning in `extract_signal_info()`
- **Empty assertion extraction**: Check `extract_assertion_from_thinking()` regex patterns if thinking models change output format
- **Wrong temporal operator**: Ensure Stage 1 specification includes timing information (registered vs combinational)
