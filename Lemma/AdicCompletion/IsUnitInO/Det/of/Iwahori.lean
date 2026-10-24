import Mathlib
import sympy.Basic
import Lemma.AdicCompletion.Support.DVRPadic

open AdicCompletionSupport

/--
[padic_iwahori_det_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
-/
@[path]
private lemma main
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ}
  {g : Matrix (Fin n) (Fin n) ℚ_[p]}
-- given
  (hn : 0 < n)
  (hdiag : ∀ i, (padicDVRContext p n hn).isUnitInO (g i i))
  (habove : ∀ i j, i < j → (padicDVRContext p n hn).isInO (g i j))
  (hbelow : ∀ i j, j < i → (padicDVRContext p n hn).isInMaxIdeal (g i j)) :
-- imply
  (padicDVRContext p n hn).isUnitInO g.det := by
-- proof
  apply padic_iwahori_det_unit n hn g hdiag habove hbelow


-- created on 2026-10-23
