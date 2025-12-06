assert property (@(posedge clk) $onehot0(gnt) |-> 1);

generate
    for (genvar i = 0; i < WIDTH; i++) begin
        as__gnt_req_match: assert property (@(posedge clk) disable iff (!rst_n)
            gnt[i] |-> req[i]
        );
    end
endgenerate

as__req_gnt_same_cycle: assert property (|req |-> |gnt);

generate
    for (genvar i = 0; i < NUM_REQS; i++) begin
        as__round_robin_arb_fairness: 
            assert property (gnt[i] && req[i] |=> gnt[i] && req[i] |-> !gnt[i] throughout ($countones(req & ~(1'b1<<i)) > 0) );
    end
endgenerate

assert property (@(posedge clk) disable iff (!rst_n) !rst_n |-> gnt == '0);

assert property ($changed(req) |-> gnt);

