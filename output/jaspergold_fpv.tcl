# ------------------------------------------------------------------
# JasperGold TCL script for formal verification of rr_arbiter_tb
# ------------------------------------------------------------------

# 1. Analyze RTL and testbench files (relative paths)
analyze -clear
analyze -sv12 design/ARBITER.sv
analyze -sv12 output/formal_verification.sv

# 2. Elaborate the design with parameters and related covers
elaborate \
    -top rr_arbiter_tb \
    -param "CLIENTS=4,NUM_REQS=4,WIDTH=8" \
    -create_related_covers {witness precondition}

# 3. Set up clock and reset signals
clock clk
reset -expression (!rst_n)

# 4. Get design information to check complexity
get_design_info

# 5. Configure proof settings
set_word_level_reduction on
set_prove_time_limit 72h   ;# Adjust as needed

# 6. Run the formal proof (full search)
prove -all

# 7. Report results
report
