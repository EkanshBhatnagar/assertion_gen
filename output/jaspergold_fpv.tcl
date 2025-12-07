# Analyze design and testbench files
analyze -clear
analyze -sv12 design/FIFO.sv
analyze -sv12 output/formal_verification.sv

# Elaborate the top-level module with parameters and related covers
elaborate -top FIFO_tb \
          -create_related_covers {witness precondition} \
          -param "FIFO_WIDTH=16,FIFO_DEPTH=8,WIDTH=8,DEPTH=16"

# Set up clock and reset signals
clock clk
reset -expression (!rst_n)

# Get design information to check general complexity
get_design_info

# Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# Run formal verification
prove -all

# Report proof results
report
