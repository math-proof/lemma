import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.Influence
open BooleanFourier


/--
[totalInfluence_eq_expected_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Influence.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, (numPivotal f x : ℝ) := by
-- proof
  unfold totalInfluence influence numPivotal
  rw [← Finset.sum_div, one_div, inv_mul_eq_div]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]


lemma BooleanFourier.totalInfluence_eq_expected_pivotal
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f = 1 / (2 : ℝ) ^ n * ∑ x : Fin n → Bool, (numPivotal f x : ℝ) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
