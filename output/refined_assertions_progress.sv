// Refined Assertions Progress
// Total assertions to process: 6
// ============================================================================

// Assertion 1
// Human description: 1. At most one bit of the gnt vector can be high in the same cycle.
assert property (@(posedge clk) $onehot0(req) |-> 1);

// Assertion 2
// Human description: 2. For each bit i, if gnt[i] is high, then req[i] must also be high in the same cycle.
generate
    for (genvar i = 0; i < WIDTH; i++) begin
    gnt_req_match: assert property (@(posedge clk) disable iff (!rst_n) gnt[i] |-> req[i] );
end
endgenerate

// Assertion 3
// Human description: 3. If any bit of req is high, then some bit of gnt must also be high in the same cycle.
as__clk_rst_n_req_gnt_same_cycle: assert property (|clk |-> |rst_n |-> |req |=> |gnt);

// Assertion 4
// Human description: 4. After gnt[i] is asserted, if req[i] remains high in the next cycle, gnt[i] can only be reasserted after all other asserted bits of req have been serviced.
generate
    for (genvar i = 0; i < NUM_REQS; i++) begin
    as__round_robin_arb_fairness: assert property (gnt[i] && req[i] |=> gnt[i] && req[i] |-> !gnt[i] throughout ($countones(req & ~(1'b1<<i)) > 0) );
end
endgenerate

// Assertion 5
// Human description: 5. When rst_n is asserted low, gnt must be all 0s in the same cycle.
assert property (@(posedge clk) disable iff (!rst_n) !rst_n |-> gnt == '0);

// Assertion 6
// Human description: 6. The gnt output must be valid in the same cycle as the req input changes, without any cycle delay.
assert property ($changed(req) |-> gnt);

