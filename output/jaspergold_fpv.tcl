# Set up environment options
set_elaborate_single_run_mode off
set_automatic_library_search on
set_analyze_libunboundsearch on
set_analyze_librescan on

# Analyze design and testbench files (relative paths)
analyze -clear
analyze -sv12 design/FIFO.sv
analyze -sv12 output/formal_verification.sv

# Elaborate the top‑level testbench with parameters and related covers
elaborate -top FIFO_tb \
          -param "WIDTH=8,DEPTH=16,FIFO_DEPTH=16" \
          -create_related_covers {witness precondition}

# Clock and reset configuration
clock clk
reset -expression (!rst_n)

# Get design complexity information
get_design_info

# Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# Proofgrid configuration (optional but recommended)
set_proofgrid_max_jobs 180
set_proofgrid_manager on

# Run formal verification
prove -all

# Report results
report