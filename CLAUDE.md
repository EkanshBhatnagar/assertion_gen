# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a **multi-stage SystemVerilog Assertion (SVA) generation pipeline** that uses LLMs to generate formal verification code from hardware design specifications. The project specifically targets a Synchronous FIFO design.

### Three-Stage Pipeline Architecture

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

# Ensure LM Studio is running on localhost:1234 for Stage 3
```

### Commands

Run each stage sequentially:

```bash
# Stage 1: Generate assertion prompts from specification
python main.py --stage 1 --spec_path design/specification.md

# Stage 2: Generate SystemVerilog assertions from prompts
python main.py --stage 2

# Stage 3: Refine assertions and generate formal verification code
python main.py --stage 3
```

Each stage depends on outputs from the previous stage stored in `output/`.

## File Structure

```
design/
  ├── FIFO.sv              # RTL design module
  └── specification.md      # Hardware specification
examples/                   # Few-shot learning examples
  ├── ft_fifo/sva/
  │   └── fifo_prop.sv     # 20 FIFO assertions
  ├── ft_mmu/sva/
  │   └── mmu_prop.sv      # 22 MMU assertions
  ├── ft_tlb/sva/
  │   └── tlb_prop.sv      # 68 TLB assertions
  └── ft_ptw/sva/
      └── ptw_prop.sv      # 118 PTW assertions
output/                     # Generated files (created by pipeline)
  ├── assertion_prompts.txt
  ├── generated_assertions.sv
  ├── refined_assertions_progress.sv  # Incremental progress
  └── formal_verification.sv
example_loader.py           # Loads and parses SVA examples
stage1.py                   # Stage 1: Spec → Prompts
stage2.py                   # Stage 2: Prompts → Assertions (uses examples)
stage3.py                   # Stage 3: Assertions → Verification (uses examples)
main.py                     # CLI entry point
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

## Common Issues

- **Stage 2/3 missing input**: Run previous stages first; pipeline is strictly sequential
- **LM Studio connection error**: Ensure LM Studio server is running on port 1234 for Stage 3
- **Signal name mismatches**: Stage 3 should fix these, but complex designs may need manual regex tuning in `extract_signal_info()`
- **Empty assertion extraction**: Check `extract_assertion_from_thinking()` regex patterns if thinking models change output format
