as__empty_after_reset: assert property (@(posedge clk) $rose(rst_n) |=> empty);

assert property (@(posedge clk) disable iff (!rst_n)
    $rose(rst_n) |=> ##1 (!full && !almost_full));

// parameter: parameter DEPTH = 16;
// parameter: parameter WIDTH = 8;
as__no_write_when_full: 
    assert property (@(posedge clk) disable iff (!rst_n)
        (wr_en && full) |=> ($stable(mem) && $stable(wr_ptr)));

assert property (@(posedge clk) disable iff (!rst_n) (full && wr_en) |-> overflow);

as__fifo_underflow: assert property (@(posedge clk) disable iff (!rst_n) (rd_en && fifo_empty) |-> underflow);

// parameter: parameter FIFO_DEPTH = 16;
assert property ( 
    @(posedge clk) disable iff (!rst_n)
    (wr_en && !full) ##1 (!wr_en [*FIFO_DEPTH-2] ##1 (rd_en && !empty)) [*FIFO_DEPTH-1] 
    |-> data_out == $past(data_in, FIFO_DEPTH-1) && $fell(full)
);

assert property (@(posedge clk) disable iff (!rst_n) $past(wr_en && !full) |=> wr_ack);

// parameter: parameter DEPTH = 8;
generate
    if (DEPTH > 1) begin
        as__almost_full:
            assert property ((DEPTH - $countones(valid)) == 1 |-> almost_full);
    end
endgenerate

// parameter: parameter DEPTH = 8;
generate
    if (DEPTH > 1) begin
        as__almost_empty:
            assert property (@(posedge clk) disable iff (!rst_n)
                ($countones(wr_ptr ^ rd_ptr) == 1) |-> almost_empty);
    end
endgenerate

// parameter: parameter DEPTH = 8;
// parameter: parameter WIDTH = 32;
as__full_fifo_rd_succeeds_next_cycle:
    assert property (@(posedge clk) disable iff (!rst_n)
        (rd_en && wr_en && full) |=> (valid_out && rd_ack));

// parameter: parameter DATA_WIDTH = 32;
// parameter: parameter DEPTH = 8;
assert property (@(posedge clk) disable iff (!rst_n)
    (rd_en && wr_en && (count == 0)) |=> 
    (wr_ack && (wr_data_reg == $past(wr_data)))
);

