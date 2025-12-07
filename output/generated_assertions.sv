// parameter: parameter NUM_REQS = 4;
assert property (@(posedge clk) $onehot0(gnt)) else $error("More than one grant asserted simultaneously");

// parameter: parameter WIDTH = 8;
generate
    for (genvar i = 0; i < WIDTH; i++) begin
        as__gnt_implies_req: 
            assert property (@(posedge clk) disable iff (!rst_n)
                gnt[i] |-> req[i]
            );
    end
endgenerate

as__req_gnt_same_cycle: assert property (|req |-> |gnt);

// parameter: parameter NUM_REQS = 4;
generate
    for (genvar i = 0; i < NUM_REQS; i++) begin
        as__round_robin_fairness:
            assert property ($past(gnt[i]) && req[i] |=> gnt[i] && ($countones(gnt) < $countones(req)));
    end
endgenerate

assert property (@(posedge clk) disable iff (~rst_n) !rst_n |-> (gnt == '0));

as__gnt_valid_same_cycle_as_req_change: 
    assert property (@(posedge clk) disable iff (!rst_n) $changed(req) |-> gnt);

