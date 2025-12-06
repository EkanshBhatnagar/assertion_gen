# Clear previous analysis state
analyze -clear

# Analyze RTL design file (SystemVerilog 2012)
analyze -sv12 design/ARBITER.sv

# Analyze testbench file (relative path)
analyze -sv12 output/formal_verification.sv

# Elaborate the design with the specified top module and requested covers
elaborate -top rr_arbiter_tb -create_related_covers {witness precondition}

# Set up clock and reset signals
clock clk
reset -expression (!rst_n)

# Get design information to check general complexity
get_design_info

# Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# (Optional) Configure ProofGrid if available
#set_proofgrid_max_jobs 180
#set_proofgrid_manager on

# Run formal verification
prove -all

# Report proof results
report
