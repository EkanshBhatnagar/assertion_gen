module rr_arbiter #(
    parameter CLIENTS = 4
)(
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [CLIENTS-1:0]   req,
    output logic [CLIENTS-1:0]   gnt
);

    logic [CLIENTS-1:0]   mask;
    logic [CLIENTS-1:0]   masked_req;
    logic [CLIENTS-1:0]   raw_gnt;
    logic [CLIENTS-1:0]   masked_gnt;
    logic [CLIENTS-1:0]   next_mask;

    // 1. Mask Generation
    // 'mask' blocks out clients that have already been served in the current
    // rotation cycle. High bits in 'mask' indicate clients having higher priority.
    assign masked_req = req & mask;

    // 2. Fixed Priority Logic (Helper)
    // Returns a grant for the lowest index bit set in the input vector.
    // FIX: Uses an iterative flag instead of variable slice r[i-1:0]
    function automatic logic [CLIENTS-1:0] get_priority_gnt(logic [CLIENTS-1:0] r);
        logic [CLIENTS-1:0] g;
        logic seen_req;

        seen_req = 1'b0;

        for (int i = 0; i < CLIENTS; i++) begin
            g[i] = r[i] && !seen_req;
            if (r[i]) seen_req = 1'b1;
        end
        return g;
    endfunction

    // 3. Calculate Grants
    // If there are requests within the high-priority mask, serve them.
    // Otherwise, wrap around and serve the raw requests (lower indices).
    always_comb begin
        masked_gnt = get_priority_gnt(masked_req);
        raw_gnt    = get_priority_gnt(req);
        
        if (|masked_req) begin
            gnt = masked_gnt;
        end else begin
            gnt = raw_gnt;
        end
    end

    // 4. Update Mask (State Machine)
    // Rotate the mask to point to the bit just AFTER the current grant.
    always_comb begin
        next_mask = mask;
        if (|gnt) begin
            // If Client k is granted, mask becomes 111...000 (0s up to k, 1s after)
            for (int i = 0; i < CLIENTS; i++) begin
                if (gnt[i]) begin
                    next_mask = '1 << (i + 1);
                end
            end
        end 
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mask <= '1; // Reset: All clients have priority
        end else begin
            mask <= next_mask;
        end
    end

endmodule