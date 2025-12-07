// parameter: parameter NUM_REQS = 4;
@(posedge clk) assert property ($onehot(gnt) |-> 1);

// parameter: parameter WIDTH = 8;
generate
    genvar i;
    for (i = 0; i < WIDTH; i++) begin : gen_gnt_req_check
        as__gnt_implies_req: assert property (@(posedge clk) disable iff (!rst_n)
            gnt[i] |-> req[i]
        );
    end
endgenerate

// parameter: parameter NUM_REQS = 4;
as__req_implies_gnt:
  assert property (@(posedge clk) disable iff (!rst_n) (|req) |-> (|gnt));

// parameter: parameter NUM_REQS = 4;
generate
    for (genvar i = 0; i < NUM_REQS; i++) begin : gen_arbitration_fairness
        as__round_robin_fairness: 
            assert property (@(posedge clk) disable iff (!rst_n)
                $past(gnt[i]) && $past(req[i]) && req[i] |->
                    !gnt[i] throughout (req[i] && !(&(gnt & req) | gnt[i]))
            );
    end
endgenerate

// parameter: parameter WIDTH = 8;
as__gnt_reset: assert property (@(posedge clk) !rst_n |-> (gnt == '0));

assert property (@(posedge clk) $past(req) != req |-> gnt);

