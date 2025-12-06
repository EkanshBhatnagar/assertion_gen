// Refined Assertions Progress
// Total assertions to process: 11
// ============================================================================

// Assertion 1
// Human description: 1. After reset is deasserted (goes high), empty should be high on the next clock cycle.
as__empty_after_reset: assert property ($rose(rst_n) |=> DUT.empty);

// Assertion 2
// Human description: 3. When a write is attempted (wr_en high) while the FIFO is full, the write data should not be stored in the FIFO on the next cycle.
assert property (@(posedge clk) (wr_en && full) |=> full);

// Assertion 3
// Human description: 4. When full is high and wr_en is high, overflow should be asserted high in the same cycle.
as__fifo_overflow: assert property (@(posedge clk) disable iff (!rst_n) (full && wr_en) |-> overflow);

// Assertion 4
// Human description: 5. When a read is attempted (rd_en high) while the FIFO is empty, underflow should be asserted high in the same cycle.
as__fifo_underflow: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && empty) |-> underflow);

// Assertion 5
// Human description: 7. When a successful write occurs (wr_en high and not full), wr_ack should be high on the next cycle.
as__wr_ack_after_successful_write: assert property (@(posedge clk) (wr_en && !full) |=> wr_ack);

// Assertion 6
// Human description: 11. When a read and write are attempted simultaneously on an empty FIFO, the write should succeed (data stored and wr_ack high) on the next cycle.
as__simultaneous_rdwr_empty_write_succeeds: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && wr_en && empty) |=> (DUT.wr_ack && !empty));

