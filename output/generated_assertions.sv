as__empty_after_reset: assert property ($rose(rst_n) |=> fifo.empty);

assert property (@(posedge clk) $rose(rst_n) |=> !full && !almost_full);

assert property (@(posedge clk) (wr_en && full) |=> full);

as__fifo_overflow: assert property (@(posedge clk) disable iff (!rst_n) (full && wr_en) |-> overflow);

as__fifo_underflow: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && empty) |-> underflow);

as__read_follows_write: 
  assert property (@(posedge clk) 
    (wr_en && !full) |-> ##(FIFO_DEPTH-1) 
      ((!$past(wr_en,1) throughout (##(FIFO_DEPTH-2))) && rd_en |-> (data_out == $past(data_in,FIFO_DEPTH-1))));

as__wr_ack_after_successful_write: assert property (@(posedge clk) (wr_en && !full) |=> wr_ack);

as__almost_full_when_one_entry_left:
    assert property ($countones(~fifo.valid) == 1 |-> fifo.almost_full);

as__fifo_almost_empty: assert property ($countones({fifo.buffer_valid_reg}) == 1 |-> fifo.almost_empty);

assert property (@(posedge clk) (full && rd_en && wr_en) |=> (!data_out_valid && rd_ack));

as__simultaneous_rdwr_empty_write_succeeds:
    assert property (@(posedge clk) disable iff (!rst_n)
        (rd_en && wr_en && empty) |=> (wr_ack && !empty));

