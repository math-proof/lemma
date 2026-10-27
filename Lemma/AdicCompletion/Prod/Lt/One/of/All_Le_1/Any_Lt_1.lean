import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AdicCompletion.Support.DVRPadic

open AdicCompletionSupport

/--
[prod_lt_one_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {f : Fin m → ℝ}
  {i₀ : Fin m}
-- given
  (hnn : ∀ i, 0 ≤ f i)
  (hle : ∀ i, f i ≤ 1)
  (hlt : f i₀ < 1) :
-- imply
  ∏ i : Fin m, f i < 1 := by
-- proof
  apply prod_lt_one_of_le_one f hnn hle hlt


-- created on 2026-10-23
