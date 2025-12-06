as__fifo_wr_ack: assert property (@(posedge clk) disable iff (!rst_n) (!full && wr_en) |-> wr_ack);

as__fifo_full_and_overflow: assert property (
    @(posedge clk) disable iff (!rst_n)
    (fifo.wr_ptr == fifo.rd_ptr) |-> (fifo.full && (fifo.wr_en |-> fifo.overflow))
);

as__fifo_read_data_correct: assert property (@(posedge clk) disable iff (!rst_n) (!empty && rd_en) |=> (data_out == mem[rd_ptr]));

as__fifo_empty: assert property (@(posedge clk) (fifo.empty |-> fifo.empty));

as__fifo_underflow: assert property (@(posedge clk) (fifo.empty && fifo.rd_en |-> fifo.underflow));

as__fifo_almostfull: assert property (@(posedge clk) disable iff (!rst_n)
                                     ($countones(valid_entries) == (DEPTH-1)) |-> almostfull);

as__fifo_almostempty: assert property (@(posedge clk) disable iff (!rst_n)
                                       $past(wr_ptr - rd_ptr == 1) |-> almostempty);

as__ctrl_reset: assert property (@(posedge clk) $past(rst_n) |-> (full == 0) && (almostfull == 0) && (empty == 1) && 
                                 (almostempty == 1) && (overflow == 0) && (underflow == 0) && (wr_ack == 0));

as__fifo_simul_access_priority: assert property (
    @(posedge clk) disable iff (!rst_n)
    (wr_en && rd_en) |-> 
        ((empty && $stable(rd_ptr) && $past(wr_ptr) != wr_ptr) ||
         (full && $stable(wr_ptr) && $past(rd_ptr) != rd_ptr))
);

as__no_simultaneous_overflow_underflow: assert property (@(posedge clk) disable iff (!rst_n) !($rose(overflow) && $rose(underflow)));

as__data_out_stable_when_not_reading: assert property (@(posedge clk) disable iff (!rst_n) !rd_en |-> $stable(data_out));

