# Set paths to DUT root and FT root (edit if needed)
set AUTOSVA_ROOT $env(AUTOSVA_ROOT)
set DUT_ROOT     $env(DUT_ROOT)

# Configure analysis options
set_elaborate_single_run_mode off
set_automatic_library_search on
set_analyze_libunboundsearch on
set_analyze_librescan on

# Analyze RTL and testbench files (relative paths)
analyze -clear
analyze -sv12 design/ARBITER.sv
analyze -sv12 output/formal_verification.sv

# Elaborate the top‑level testbench with parameters
elaborate -top rr_arbiter_tb \
          -create_related_covers {witness precondition} \
          -param "CLIENTS=4,NUM_REQS=4,WIDTH=8"

# Set up clock and reset signals
clock clk
reset -expression (!rst_n)

# Get design information to check general complexity
get_design_info

# Proof settings
set_word_level_reduction on
set_prove_time_limit 72h
set_proofgrid_max_jobs 180
set_proofgrid_manager on

# Run the formal verification
prove -all

# Report results
report
