import Mathlib
import sympy.Basic
import Lemma.AdicCompletion.Support.DVRPadic

open AdicCompletionSupport

/--
[iwahori_det_norm_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
-/
@[path]
private lemma main
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {m : ℕ}
  {g : Matrix (Fin m) (Fin m) ℚ_[p]}
-- given
  (hdiag : ∀ i, ‖g i i‖ = 1)
  (habove : ∀ i j, i < j → ‖g i j‖ ≤ 1)
  (hbelow : ∀ i j, j < i → ‖g i j‖ < 1) :
-- imply
  ‖g.det‖ = 1 := by
-- proof
  apply iwahori_det_norm_eq_one p g hdiag habove hbelow


-- created on 2026-10-23
