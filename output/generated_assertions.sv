as__fifo_write_ack: assert property (@(posedge clk) disable iff (!rst_n) (!full && wr_en) |-> wr_ack);

as__fifo_full_and_overflow: assert property (@(posedge clk) disable iff (!rst_n)
    (fifo_full == 1) |-> (full == 1) && ((fifo_full && write_en) |-> (overflow == 1)));

as__fifo_data_out_matches_expected:
  assert property (@(posedge clk) disable iff (!rst_n)
    fifo_not_empty && rd_en |-> data_out == $past(fifo_mem[rd_ptr]));

as__fifo_empty_underflow: assert property (@(posedge clk) disable iff (!rst_n) empty |-> (read_en |-> underflow));

as__fifo_almostfull: assert property ($countones(fifo.mem) == FIFO_DEPTH-1 |-> fifo.almostfull);

as__fifo_almostempty: assert property ($countones(fifo.slots) == 1 |-> fifo.almostempty);

as__fifo_ctrl_signals_after_reset: assert property (
  @(posedge clk) disable iff (!rst_n)
  $past(rst_n) && !rst_n |=> 
    !full && !almostfull && !overflow &&
    empty && almostempty && !underflow && !wr_ack
);

as__fifo_simultaneous_wr_rd_priority: assert property (
  @(posedge clk) disable iff (!rst_n)
    (wr_en && rd_en && !full && empty) |-> !empty,
    (wr_en && rd_en && full && !empty) |-> !full
);

as__no_overflow_underflow: assert property (@(posedge clk) !(overflow && underflow));

as__data_out_stable_without_rd_en: assert property (!rd_en |-> $stable(data_out));

