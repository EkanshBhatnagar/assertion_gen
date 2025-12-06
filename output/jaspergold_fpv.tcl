# --------------------------------------------------------------------
# JasperGold Formal Verification Script for FIFO_tb
# --------------------------------------------------------------------

# Optional: set environment variables (can be omitted if not used)
set AUTOSVA_ROOT $env(AUTOSVA_ROOT)
set DUT_ROOT     $env(DUT_ROOT)

# --------------------------------------------------------------------
# 1. Analyze Design Sources
# --------------------------------------------------------------------
analyze -clear
analyze -sv12 /Users/ekanshb/Documents/Projects/assertion_gen/design/FIFO.sv
analyze -sv12 /Users/ekanshb/Documents/Projects/assertion_gen/output/formal_verification.sv

# --------------------------------------------------------------------
# 2. Elaborate Design (top-level is the testbench)
# --------------------------------------------------------------------
elaborate -top FIFO_tb \
          -create_related_covers {witness precondition} \
          -auto_hr_info

# --------------------------------------------------------------------
# 3. Clock and Reset Setup
# --------------------------------------------------------------------
clock clk
reset -expression (!rst_n)

# --------------------------------------------------------------------
# 4. Design Information (complexity check)
# --------------------------------------------------------------------
get_design_info

# --------------------------------------------------------------------
# 5. Proof Settings
# --------------------------------------------------------------------
set_word_level_reduction on
set_prove_time_limit 72h          ;# Adjust as needed

# Optional: enable ProofGrid parallelism if available
set_proofgrid_max_jobs 180
set_proofgrid_manager on

# --------------------------------------------------------------------
# 6. Run Formal Verification
# --------------------------------------------------------------------
autoprove -all -bg

# --------------------------------------------------------------------
# 7. Report Results
# --------------------------------------------------------------------
report
