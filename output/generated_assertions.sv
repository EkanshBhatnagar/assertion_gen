assert property (@(posedge clk) $rose(rst_n) |=> empty);

@(posedge clk) 
    assert property (!reset |=> !full && !almost_full);

// parameter: parameter WIDTH = 8;
// parameter: parameter DEPTH = 16;
@(posedge clk)
assert property (
    (wr_en && full) |=> (rd_data != $past(wr_data))
);

assert property (@(posedge clk) (full && wr_en) |-> overflow);

as__fifo_underflow: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && empty) |-> underflow);

// parameter: parameter FIFO_DEPTH = 16;
assert property (@(posedge clk) 
    wr_en && !full |-> ##(FIFO_DEPTH-1) 
        (!wr_en [*FIFO_DEPTH-1]) ##1 rd_en && !empty |-> data_out == $past(data_in, FIFO_DEPTH));

as__wr_ack_next_cycle: assert property (@(posedge clk) disable iff (!rst_n) 
                                        (wr_en && !full) |=> wr_ack);

// parameter: parameter DEPTH = 16;
as__fifo_almost_full: assert property (
    @(posedge clk) disable iff (!rst_n)
    (fifo.wr_ptr - fifo.rd_ptr == DEPTH - 1) |-> fifo.almost_full
);

// parameter: parameter DEPTH = 8;
assert property (@(posedge clk) (wr_ptr - rd_ptr == 1) |-> almost_empty);

as__read_succeeds_on_full_fifo_conflict:
    assert property (@(posedge clk) disable iff (!rst_n)
        (rd_en && wr_en && full) |=> (data_out_valid && rd_ack));

as__write_succeeds_on_simultaneous_read_write_empty:
    assert property (@(posedge clk) disable iff (!rst_n)
        (rd_en && wr_en && empty) |=> wr_ack);

