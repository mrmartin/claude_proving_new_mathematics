/-
**Axiom-cleanness checks** for the ported / re-proved Parthasarathy
lemmas. Every theorem here should depend on only the standard
foundational axioms `[propext, Classical.choice, Quot.sound]`.

(The `sorry`-bodied theorems — `caseB_split_naive`,
`caseB_split_with_hyp`, `erdos_699_main`, `pure_power_dichotomy_M_ge_2`,
`dichotomy_closes_FO_residual` — are deliberately excluded; they will
report `sorryAx` until closed.)
-/

import Erdos699.Master
import Erdos699.Tame
import Erdos699.Carry
import Erdos699.Absorption
import Erdos699.FullyObstructed
import Erdos699.CaseB
import Erdos699.Stijn
import Erdos699.Fix2_i2

namespace Erdos699

#print axioms master_identity
#print axioms prime_not_dvd_factorial
#print axioms tame_prime
#print axioms dvd_choose_of_dvd_residual_block
#print axioms carry_lemma
#print axioms carry_lemma_at_p
#print axioms carry_lemma_fo_resolution
#print axioms absorption
#print axioms dvd_choose_of_dvd_n_not_dvd_j
#print axioms case_B_alpha
#print axioms case_B_alpha_gcd
#print axioms caseB_split_with_hyp_tame_residual
#print axioms fo_char
#print axioms fo_28_5_14
#print axioms fo_2188_3_1094
#print axioms stijn_spirit_obstruction_witness
#print axioms exists_odd_prime_dvd_of_coprime_two
#print axioms odd_prime_dvd_choose_two
#print axioms dichotomy_M_ge_2_witness
#print axioms dvd_choose_of_dichotomy_digit_zero_mismatch
#print axioms dvd_choose_of_lucas_mismatch_at

end Erdos699
