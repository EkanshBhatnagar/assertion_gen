# Synchronous FIFO

## Overview

This project involves the verification of a **Synchronous FIFO** design using SystemVerilog. The goal was to ensure the correctness of the design by implementing a comprehensive testbench, including coverage, assertions, and various checks to verify underflow, overflow, and other edge conditions.

### Key Features of the FIFO:
- **FIFO_WIDTH**: Data in/out and memory word width (default: 16)
- **FIFO_DEPTH**: Memory depth (default: 8)

### Ports:

| Port       | Direction | Function                                                                                     |
|------------|-----------|----------------------------------------------------------------------------------------------|
| data_in    | Input     | Write Data: The input data bus used when writing the FIFO.                                    |
| wr_en      | Input     | Write Enable: If the FIFO is not full, asserting this signal causes data to be written in.    |
| rd_en      | Input     | Read Enable: If the FIFO is not empty, asserting this signal causes data to be read out.      |
| clk        | Input     | Clock signal.                                                                                 |
| rst_n      | Input     | Active low asynchronous reset.                                                                |
| data_out   | Output    | Read Data: The sequential output data bus used when reading from the FIFO.                    |
| full       | Output    | Full Flag: Indicates that the FIFO is full.                                                   |
| almostfull | Output    | Almost Full: Indicates that only one more write can be performed before the FIFO is full.     |
| empty      | Output    | Empty Flag: Indicates that the FIFO is empty.                                                 |
| almostempty| Output    | Almost Empty: Indicates that only one more read can be performed before the FIFO is empty.    |
| overflow   | Output    | Indicates that a write request was rejected because the FIFO is full.                        |
| underflow  | Output    | Indicates that a read request was rejected because the FIFO is empty.                        |
| wr_ack     | Output    | Write Acknowledge: Indicates that a write request succeeded.                                  |

### Behavior:
- If both `rd_en` and `wr_en` are high, the FIFO will prioritize writing if empty and reading if full.
- The **FIFO** design includes checks for underflow and overflow conditions.
