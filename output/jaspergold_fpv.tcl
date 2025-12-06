# ------------------------------------------------------------
# JasperGold Formal Verification Script for FIFO_tb
# ------------------------------------------------------------

# 1. Analyze design files (clear previous analysis)
analyze -clear
analyze -sv12 design/FIFO.sv
analyze -sv12 output/formal_verification.sv

# 2. Elaborate the design with related covers
elaborate -top FIFO_tb -create_related_covers {witness precondition}

# 3. Clock and reset configuration
clock clk
reset -expression (!rst_n)

# 4. Get design information (complexity check)
get_design_info

# 5. Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# Optional: increase parallelism if available
#set_proofgrid_max_jobs 180
#set_proofgrid_manager on

# 6. Run the formal proof (full proof, not auto)
prove -all

# 7. Report results
report
