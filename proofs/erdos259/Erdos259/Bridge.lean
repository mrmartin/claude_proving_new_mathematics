/-
Bridge from `Erdos259.Gist.erdos_259` (ster-oc gist) to upstream
`Erdos259.erdos_259`. Upstream uses `μ n` (notation for `moebius n`);
gist uses `moebius n` directly. Same `Irrational` conclusion.
-/

import Erdos259.Proof
import Mathlib

namespace Erdos259

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/--
**Erdős Problem 259** — `∑ μ(n)² · n / 2ⁿ` is irrational.
Upstream signature.
-/
theorem erdos_259 : Irrational (∑' n : ℕ, (μ n) ^ 2 * n / (2 ^ n)) := by
  have h := Gist.erdos_259
  convert h using 1
  congr 1; ext n; push_cast; ring

end Erdos259
