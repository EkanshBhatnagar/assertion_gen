// Refined Assertions Progress
// Total assertions to process: 11
// ============================================================================

// Assertion 1
// Human description: 1. After reset is deasserted (goes high), empty should be high on the next clock cycle.
as__empty_after_reset: assert property ($rose(rst_n) |=> fifo.empty);

// Assertion 2
// Human description: 2. After reset is deasserted (goes high), full and almost full should be low on the next clock cycle.
assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);

// Assertion 3
// Human description: 3. When a write is attempted (wr_en high) while the FIFO is full, the write data should not be stored in the FIFO on the next cycle.
assert property (@(posedge clk) (wr_en && full) |=> full);

// Assertion 4
// Human description: 4. When full is high and wr_en is high, overflow should be asserted high in the same cycle.
as__fifo_overflow: assert property (@(posedge clk) disable iff (!rst_n) (full && wr_en) |-> overflow);

// Assertion 5
// Human description: 5. When a read is attempted (rd_en high) while the FIFO is empty, underflow should be asserted high in the same cycle.
as__fifo_underflow: assert property (@(posedge clk) disable iff (!rst_n) (DUT.rd_en && DUT.empty) |-> DUT.underflow);

// Assertion 6
// Human description: 6. When a successful write occurs (wr_en high and not full), the same data should appear on data_out after FIFO_DEPTH-1 successive reads, assuming no other writes occur.
as__read_follows_write: assert property (@(posedge clk) (wr_en && !full) |-> ##(FIFO_DEPTH-1) ((!$past(wr_en,1) throughout (##(FIFO_DEPTH-2))) && rd_en |-> (data_out == $past(data_in,FIFO_DEPTH-1))));

// Assertion 7
// Human description: 7. When a successful write occurs (wr_en high and not full), wr_ack should be high on the next cycle.
as__wr_ack_after_successful_write: assert property (@(posedge clk) (DUT.wr_en && !DUT.full) |=> DUT.wr_ack);

// Assertion 8
// Human description: 8. When there is one empty entry in the FIFO, almost_full should be asserted high in the same cycle.
as__almost_full_when_one_entry_left: assert property (@(posedge clk) (DUT.count == FIFO_DEPTH-1) |-> DUT.almostfull);

// Assertion 9
// Human description: 9. When there is only one occupied entry in the FIFO, almost_empty should be asserted high in the same cycle.
as__fifo_almost_empty: assert property (@(posedge clk) (DUT.count == 1) |-> DUT.almostempty);

// Assertion 10
// Human description: 10. When a read and write are attempted simultaneously on a full FIFO, the read should succeed (data_out valid and rd_ack high) on the next cycle.
assert property (@(posedge clk) (full && rd_en && wr_en) |=> (!data_out_valid && rd_ack));

// Assertion 11
// Human description: 11. When a read and write are attempted simultaneously on an empty FIFO, the write should succeed (data stored and wr_ack high) on the next cycle.
as__simultaneous_rdwr_empty_write_succeeds: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && wr_en && empty) |=> (wr_ack && !empty));

