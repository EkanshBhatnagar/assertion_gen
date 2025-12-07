# ------------------------------------------------------------------
# JasperGold Formal Verification Script for rr_arbiter_tb
# ------------------------------------------------------------------

# 1. Analyze design and testbench files (relative paths)
analyze -clear
analyze -sv12 design/ARBITER.sv
analyze -sv12 output/formal_verification.sv

# 2. Elaborate the top‑level module
elaborate -top rr_arbiter_tb \
          -create_related_covers {witness precondition}

# 3. Set up clock and reset signals
clock clk
reset -expression (!rst_n)

# 4. Get design information (complexity check)
get_design_info

# 5. Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# Optional: enable ProofGrid if available
# set_proofgrid_max_jobs 180
# set_proofgrid_manager on

# 6. Run the formal proof
prove -all

# 7. Report results
report
