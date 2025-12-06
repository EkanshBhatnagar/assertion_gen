// Refined Assertions Progress
// Total assertions to process: 22
// ============================================================================

// Assertion 1
// Human description: 1. Assert that when the FIFO is not full and wr_en is asserted, the wr_ack signal is also asserted.
assert property (
    @(posedge clk)
    disable iff (!DUT.rst_n)
    (!DUT.full && DUT.wr_en) |-> DUT.wr_ack
);

// Assertion 2
// Human description: 3. Assert that when the FIFO is not empty and rd_en is asserted, the data_out matches the expected value based on the FIFO's internal state.
assert property (
    !DUT.empty && DUT.rd_en |-> DUT.data_out == $past(DUT.mem[DUT.wr_ptr - 1])
);

// Assertion 3
// Human description: 4. Assert that when the FIFO is empty, the empty signal is asserted, and any further read attempts result in the underflow signal being asserted.
assert property (@(posedge clk) disable iff (!rst_n)
    (DUT.empty & DUT.rd_en) |-> DUT.underflow);

// Assertion 4
// Human description: 5. Assert that when the FIFO has only one empty slot left, the almostfull signal is asserted.
assert property (@(posedge clk)
    (DUT.count == 7) |-> DUT.almostfull);

// Assertion 5
// Human description: 6. Assert that when the FIFO has only one occupied slot left, the almostempty signal is asserted.
assert property (@(posedge clk) (DUT.count == 1'b1 |-> DUT.almostempty));

// Assertion 6
// Human description: 8. Assert that when both wr_en and rd_en are asserted simultaneously, the FIFO prioritizes writing if it is empty and reading if it is full.
assert property (
  @(posedge clk) disable iff (!rst_n)
  (DUT.wr_en && DUT.rd_en && DUT.empty)
  |=> (DUT.count == $past(DUT.count)+1'b1)
);

// Assertion 7
// Human description: 10. Assert that the data_out remains stable when rd_en is not asserted.
assert property (@(posedge clk) (!DUT.rd_en |-> $stable(DUT.data_out)));

// Assertion 8
// Human description: No description available
assert property (@(posedge clk) (DUT.empty && DUT.rd_en) |-> DUT.underflow);

// Assertion 9
// Human description: No description available
assert property (@(posedge clk) disable iff (!rst_n)
    (DUT.almostfull |=> (DUT.count >= 7)));

// Assertion 10
// Human description: No description available
assert property (
  (DUT.count == DUT.FIFO_DEPTH-1) |-> DUT.almostfull
);

// Assertion 11
// Human description: No description available
assert property (@(posedge clk) disable iff (!rst_n)
    (DUT.almostempty |-> ##0 (DUT.count <= 2)));

// Assertion 12
// Human description: No description available
assert property (@(posedge clk)
    $past(DUT.count == 1) |-> DUT.almostempty);

// Assertion 13
// Human description: No description available
assert property (@(posedge clk)
  $past(rst_n) |-> (full == 1'b0 && almostfull == 1'b0 && empty == 1'b1));

// Assertion 14
// Human description: No description available
assert property (@(posedge DUT.clk) (DUT.almostempty && !DUT.overflow && !DUT.underflow && !DUT.wr_ack));

// Assertion 15
// Human description: No description available
assert property (@(posedge clk)
  ((DUT.wr_en && DUT.rd_en && DUT.rst_n) |-> !DUT.overflow && !DUT.underflow));

// Assertion 16
// Human description: No description available
(Empty – no assertion can be generated without a description.)

// Assertion 17
// Human description: No description available
assert property (@(posedge clk)
    disable iff (!rst_n)
    (wr_en && rd_en) |-> $stable(DUT.count));

// Assertion 18
// Human description: No description available
assert property (@(posedge clk)
    (DUT.empty & $stable(DUT.count) |=> ($past(DUT.wr_ptr) == DUT.wr_ptr)));

// Assertion 19
// Human description: No description available
assert property (@(posedge clk)
    disable iff (!DUT.rst_n)
    (DUT.full && $stable(DUT.wr_ptr) && ($past(DUT.count) != DUT.count))
);

// Assertion 20
// Human description: No description available
assert property (@(posedge clk) disable iff (!rst_n) (DUT.wr_en |=> DUT.wr_ack));

// Assertion 21
// Human description: No description available
assert property (@(posedge clk) disable iff (!rst_n) !($rose(DUT.overflow) && $rose(DUT.underflow)));

// Assertion 22
// Human description: No description available
assert property (@(posedge DUT.clk) disable iff (!DUT.rst_n) !DUT.rd_en |-> $stable(DUT.data_out));

