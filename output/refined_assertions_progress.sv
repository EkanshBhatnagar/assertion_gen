// Refined Assertions Progress
// Total assertions to process: 11
// ============================================================================

// Assertion 1
// Human description: 1. After reset is deasserted (goes high), empty should be high on the next clock cycle.
assert property (@(posedge clk) $rose(rst_n) |=> empty);

// Assertion 2
// Human description: 4. When full is high and wr_en is high, overflow should be asserted high in the same cycle.
assert property (@(posedge clk) (full && wr_en) |-> overflow);

// Assertion 3
// Human description: 5. When a read is attempted (rd_en high) while the FIFO is empty, underflow should be asserted high in the same cycle.
as__fifo_underflow: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && empty) |-> underflow);

// Assertion 4
// Human description: 7. When a successful write occurs (wr_en high and not full), wr_ack should be high on the next cycle.
as__wr_ack_next_cycle: assert property (@(posedge clk) disable iff (!rst_n) (wr_en && !full) |=> wr_ack);

// Assertion 5
// Human description: 11. When a read and write are attempted simultaneously on an empty FIFO, the write should succeed (data stored and wr_ack high) on the next cycle.
as__write_succeeds_on_simultaneous_read_write_empty: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && wr_en && empty) |=> wr_ack);

