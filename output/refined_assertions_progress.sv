// Refined Assertions Progress
// Total assertions to process: 17
// ============================================================================

// Assertion 1
// Human description: 1. After reset is deasserted (goes high), empty should be high on the next clock cycle.
assert property ($rose(DUT.rst_n) |=> DUT.empty);

// Assertion 2
// Human description: 3. When a write is attempted (wr_en high) while the FIFO is full, the write data should not be stored in the FIFO on the next cycle.
assert property (@(posedge clk)
    (DUT.wr_en && DUT.full) |=> ##1 (DUT.count == $past(DUT.count))
);

// Assertion 3
// Human description: 5. When a read is attempted (rd_en high) while the FIFO is empty, underflow should be asserted high in the same cycle.
assert property (@(posedge clk) ((DUT.rd_en && DUT.empty)) |-> DUT.underflow);

// Assertion 4
// Human description: 7. When a successful write occurs (wr_en high and not full), wr_ack should be high on the next cycle.
assert property (@(posedge clk) disable iff (!rst_n) (DUT.wr_en && !DUT.full) |-> ##1 DUT.wr_ack);

// Assertion 5
// Human description: 9. When there is only one occupied entry in the FIFO, almost_empty should be asserted high in the same cycle.
assert property (
    @(posedge clk)
    disable iff (!rst_n)
    (DUT.count == 1'b1) |-> almostempty
);

// Assertion 6
// Human description: 11. When a read and write are attempted simultaneously on an empty FIFO, the write should succeed (data stored and wr_ack high) on the next cycle.
assert property (@(posedge clk)
  (DUT.wr_en && DUT.rd_en && DUT.empty) |=> ##1 DUT.wr_ack);

// Assertion 7
// Human description: No description available
assert property (@(posedge DUT.clk) disable iff (!DUT.rst_n)
    (DUT.wr_en && !DUT.full) |=> DUT.wr_ack);

// Assertion 8
// Human description: No description available
assert property (@(posedge clk)
    (DUT.wr_en && !DUT.full) |-> ##7);

// Assertion 9
// Human description: No description available
assert property (@(posedge clk)
  (! $past(DUT.wr_en,1) throughout ##(DUT.FIFO_DEPTH-2)) |-> (DUT.rd_en |=> (DUT.data_out == $past(DUT.data_in,DUT.FIFO_DEPTH-1)))
);

// Assertion 10
// Human description: No description available
assert property (@(posedge clk) (DUT.wr_en && !DUT.full) |=> DUT.wr_ack);

// Assertion 11
// Human description: No description available
assert property (@(posedge clk)
    (DUT.count == FIFO_DEPTH-1) |-> ##0 DUT.almostfull);

// Assertion 12
// Human description: No description available
assert property ($countones(~DUT.valid) == 1 |-> DUT.almostfull);

// Assertion 13
// Human description: No description available
assert property ((DUT.count == 1) |-> DUT.almostempty);

// Assertion 14
// Human description: No description available
assert property (@(posedge clk)
    (DUT.full && DUT.rd_en && DUT.wr_en) |=> (!DUT.wr_ack));

// Assertion 15
// Human description: No description available
assert property (@(posedge clk)
  (DUT.empty && DUT.wr_en && DUT.rd_en) |-> (DUT.wr_ack && !DUT.underflow));

// Assertion 16
// Human description: No description available
assert property (@(posedge clk) disable iff (!DUT.rst_n)
    (DUT.wr_en && !DUT.full) |-> ##0 (DUT.wr_ack));

// Assertion 17
// Human description: No description available
assert property (@(posedge clk)
    (DUT.rd_en && DUT.wr_en && DUT.empty) |=> (DUT.wr_ack && !DUT.empty));

