module

import ChristodoulouBV

/-!
# Axiom audit

Run with `lake env lean scripts/AxiomAudit.lean`. Each of the four main theorems must depend exactly on
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms). `scripts/check.sh` compares the output.
-/

#print axioms ChristodoulouBV.theorem3_1_unique
#print axioms ChristodoulouBV.theorem3_1_extend
#print axioms ChristodoulouBV.theorem5_1
#print axioms ChristodoulouBV.theorem6_1_6_2_exists
