# Analyze design files
analyze -clear
analyze -sv12 design/FIFO.sv
analyze -sv12 output/formal_verification.sv

# Elaborate design
elaborate -top FIFO_tb -create_related_covers {witness precondition}

# Clock and reset configuration
clock clk
reset -expression (!rst_n)

# Get design information to check complexity
get_design_info

# Proof settings
set_word_level_reduction on
set_prove_time_limit 72h

# Run formal verification
prove -all

# Report proof results
report
