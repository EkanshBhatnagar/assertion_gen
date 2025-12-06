// Refined Assertions Progress
// Total assertions to process: 22
// ============================================================================

// Assertion 1
// Human description: 1. Assert that when the FIFO is not full and wr_en is asserted, the wr_ack signal is also asserted.
assert property (@(posedge clk) disable iff (!rst_n) (!DUT.full && DUT.wr_en) |-> DUT.wr_ack);

// Assertion 2
// Human description: 3. Assert that when the FIFO is not empty and rd_en is asserted, the data_out matches the expected value based on the FIFO's internal state.
assert property (@(posedge clk)
    disable iff (!rst_n)
      (|!DUT.empty && DUT.rd_en |-> DUT.data_out == $past(DUT.data_in))
  );

// Assertion 3
// Human description: 4. Assert that when the FIFO is empty, the empty signal is asserted, and any further read attempts result in the underflow signal being asserted.
as__fifo_empty_underflow: assert property @ (posedge clk)

// Assertion 4
// Human description: 6. Assert that when the FIFO has only one occupied slot left, the almostempty signal is asserted.
assert property (@(posedge clk) (DUT.count == 4'b0001 |-> DUT.almostempty));

// Assertion 5
// Human description: 7. Assert that after a reset (rst_n asserted), all control signals (full, almostfull, empty, almostempty, overflow, underflow, wr_ack) are properly initialized to their default values.
assert property (@(posedge clk) disable iff (!rst_n)
    (rst_n && !$past(rst_n)) |-> (
        DUT.full          == 1'b0 &&
        DUT.almostfull    == 1'b0 &&
        DUT.empty         == 1'b1 &&
        DUT.almostempty   == 1'b1 &&
        DUT.overflow      == 1'b0 &&
        DUT.underflow     == 1'b0 &&
        DUT.wr_ack        == 1'b0
    )
);

// Assertion 6
// Human description: 8. Assert that when both wr_en and rd_en are asserted simultaneously, the FIFO prioritizes writing if it is empty and reading if it is full.
assert property (@(posedge clk)
  ((DUT.wr_en && DUT.rd_en) |-> 
   ( ($past(DUT.empty) && (DUT.count == $past(DUT.count)+1'b1)) ||
     ($past(DUT.full)   && (DUT.count == $past(DUT.count)-1'b1)) )
  );

// Assertion 7
// Human description: 10. Assert that the data_out remains stable when rd_en is not asserted.
assert property (
    @(posedge clk)
    disable iff (!rst_n)
    ~DUT.rd_en |-> (DUT.data_out == $past(DUT.data_out))
);

// Assertion 8
// Human description: No description available
assert property (DUT.count == FIFO_DEPTH-1 |-> DUT.almostfull);

// Assertion 9
// Human description: No description available
assert property (DUT.count == 1 |-> DUT.almostempty);

// Assertion 10
// Human description: No description available
assert property (
  @(posedge clk)
  disable iff (!rst_n)
  (rst_n |=> ##[1:2] (DUT.empty && DUT.count == '0 && DUT.wr_ptr == '0))
);

// Assertion 11
// Human description: No description available
(Empty – no assertion can be generated without a description.)

// Assertion 12
// Human description: No description available
assert property (as__fifo_reset_empty:
    $past(DUT.rst_n) && !DUT.rst_n |=> DUT.empty);

// Assertion 13
// Human description: No description available
assert property (@(posedge DUT.clk)
  disable iff (!DUT.rst_n)
    (DUT.wr_en && !DUT.full && !DUT.almostfull && !DUT.overflow |=> DUT.wr_ack));

// Assertion 14
// Human description: No description available
assert property (@(posedge clk) DUT.empty |-> (DUT.almostempty && !DUT.underflow && !DUT.wr_ack));

// Assertion 15
// Human description: No description available
assert property (@(posedge clk) disable iff (!rst_n) (DUT.wr_en |=> DUT.wr_ack));

// Assertion 16
// Human description: No description available
assert property (
  @(posedge DUT.clk)
  (DUT.wr_en && DUT.rd_en) |-> (DUT.count == $past(DUT.count)+1'b1)
);

// Assertion 17
// Human description: No description available
(Empty – no assertion can be generated without a description.)

// Assertion 18
// Human description: No description available
assert property (@(posedge clk)
  ((DUT.wr_en && DUT.rd_en && !DUT.full && DUT.empty) |-> !DUT.empty));

// Assertion 19
// Human description: No description available
assert property (@(posedge DUT.clk)
    (DUT.wr_en && DUT.rd_en && DUT.full && !DUT.empty) |-> !DUT.full);

// Assertion 20
// Human description: No description available
assert property (@(posedge clk) disable iff (!rst_n) (DUT.wr_en |=> DUT.wr_ack));

// Assertion 21
// Human description: No description available
assert property (@(posedge DUT.clk) !(DUT.overflow && DUT.underflow));

// Assertion 22
// Human description: No description available
assert property (!DUT.rd_en |-> $stable(DUT.data_out));

