# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.09
# platform  : Linux 4.18.0-553.69.1.el8_10.x86_64
# version   : 2024.09 FCS 64 bits
# build date: 2024.09.26 14:35:17 UTC
# ----------------------------------------
# started   : 2025-12-06 16:33:07 CST
# hostname  : n04-hades.olympus.ece.tamu.edu.(none)
# pid       : 2081199
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:45917' '-style' 'windows' '-data' 'AAAAjHicY2RgYLCp////PwMYMD6A0Aw2jAyoAMRnQhUJbEChGRhYYZqRNakwZDEkMhQzFDCkMhQxpDPkM+QwpDDEM6QBRcoY9BhKGJKBIiAAALTTDiw=' '-proj' '/home/grads/e/ekanshb/assertion_gen/output/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/grads/e/ekanshb/assertion_gen/output/jgproject/.tmp/.initCmds.tcl' 'jaspergold_fpv.tcl'
# ------------------------------------------------------------------
# JasperGold TCL Script for Formal Verification of FIFO_tb
# ------------------------------------------------------------------

# 1. Analyze RTL and Testbench (relative paths)
analyze -clear
analyze -sv12 ../design/FIFO.sv
analyze -sv12 ../output/formal_verification.sv

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
