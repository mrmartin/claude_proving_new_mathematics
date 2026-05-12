/-
**Stijn's bug witness.** StijnC's 2026-05-01 forum comment on
`erdosproblems.com/forum/thread/699`:

> "In Case B: when `i < q < j`, it may be that `C(n, j)` and
> `C(n-i, j-i)` are not multiples of `q`, while `C(j, i)` and `C(n, i)`
> are. E.g., assume `q = j - k_j` and `q | n - k_n` where
> `k_j < k_n < i` and `v_q(n - k_n) = 1`."

The strict form (`k_j < k_n < i`) requires `i ≥ 2` and distinct hit
indices in the i-block and j-block.

We document the *spirit* example `(n, i, j, q) = (10, 3, 5, 5)` here
(it has `k_j = k_n = 0`, violating strict `k_j < k_n` but matching every
other Stijn predicate: simultaneous v_q = 1 on i- and j-blocks with
empty (j-i)-block, and `q ∤ C(n, j)`). A search for a strict-form
example over small `(n, i, j)` is a follow-up to this file.
-/

import Erdos699.CaseB
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Erdos699

open Nat

/-! ## Spirit example: `(n, i, j, q) = (10, 3, 5, 5)`

* `i`-block `{10, 9, 8}` — `5 ∣ 10` (with `v_5 = 1`), `5 ∤ 9`, `5 ∤ 8`.
* `j`-block `{5, 4, 3}` — `5 ∣ 5` (with `v_5 = 1`), `5 ∤ 4`, `5 ∤ 3`.
* `(j-i)`-block `{7, 6}` — no multiple of `5`.

So `5 ∣ C(10, 3)` (single hit at `n - 0 = 10`), `5 ∣ C(5, 3)`
(single hit at `j - 0 = 5`), `5 ∤ C(7, 2)`, and by the master-identity
valuation form `v_5(C(10, 5)) = v_5(C(10, 3)) + v_5(C(7, 2)) -
v_5(C(5, 3)) = 1 + 0 - 1 = 0`. Hence `5 ∤ C(10, 5)`.

Numerically: `C(10, 3) = 120 = 2³·3·5`, `C(5, 3) = 10 = 2·5`,
`C(7, 2) = 21 = 3·7`, `C(10, 5) = 252 = 2²·3²·7`. -/

theorem stijn_spirit_i_block :
    (5 : ℕ) ∣ Nat.choose 10 3 := by native_decide

theorem stijn_spirit_j_block :
    (5 : ℕ) ∣ Nat.choose 5 3 := by native_decide

theorem stijn_spirit_residual_empty :
    ¬ ((5 : ℕ) ∣ Nat.choose 7 2) := by native_decide

theorem stijn_spirit_q_not_witness :
    ¬ ((5 : ℕ) ∣ Nat.choose 10 5) := by native_decide

/-- The spirit example `(10, 3, 5, 5)` satisfies the four predicates
`5 ∣ C(10, 3) ∧ 5 ∣ C(5, 3) ∧ ¬ 5 ∣ C(7, 2) ∧ ¬ 5 ∣ C(10, 5)`. This is
exactly the negation of "tame prime `q = 5` witnesses
`gcd(C(n, i), C(n, j))`" — Stijn's bug, structurally.

Note: the triple `(10, 3, 5)` is also a known FO triple. The Carry
Lemma (`carry_lemma_fo_resolution`) supplies `p = 3` as an alternative
witness via the `M = 1` structure `10 - 1 = 3²`. So this *spirit
example* refutes the naive Case-B claim but does not refute Erdős
#699 itself: there is still a witnessing prime (`3`), just not the
tame prime `5`. -/
theorem stijn_spirit_obstruction_witness :
    (5 : ℕ) ∣ Nat.choose 10 3 ∧
    (5 : ℕ) ∣ Nat.choose 5 3 ∧
    ¬ ((5 : ℕ) ∣ Nat.choose 7 2) ∧
    ¬ ((5 : ℕ) ∣ Nat.choose 10 5) := by
  refine ⟨stijn_spirit_i_block, stijn_spirit_j_block,
          stijn_spirit_residual_empty, stijn_spirit_q_not_witness⟩

end Erdos699
