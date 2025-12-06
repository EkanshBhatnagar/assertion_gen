# ------------------------------------------------------------------
# JasperGold TCL Script for Formal Verification of FIFO_tb
# ------------------------------------------------------------------

# 1. Analyze RTL and Testbench (relative paths)
analyze -clear
analyze -sv12 design/FIFO.sv
analyze -sv12 output/formal_verification.sv

# 2. Elaborate the design with related covers
elaborate -top FIFO_tb -create_related_covers {witness precondition}

# 3. Set up clock and reset signals
clock clk
reset -expression (!rst_n)

# 4. Get design information to check complexity
get_design_info

# 5. Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# Optional: configure ProofGrid (if available)
set_proofgrid_max_jobs 180
set_proofgrid_manager on

# 6. Run formal verification
prove -all

# 7. Report results
report
