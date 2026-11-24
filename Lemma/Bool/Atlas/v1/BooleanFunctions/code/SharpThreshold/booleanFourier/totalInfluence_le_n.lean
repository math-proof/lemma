import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.SharpThreshold.booleanFourier.influence_le_one
open BooleanFourier Finset Bool


/--
[totalInfluence_le_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/SharpThreshold.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f ≤ (n : ℝ) := by
-- proof
  show ∑ i : Fin n, influence f i ≤ (n : ℝ)
  calc
    _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => influence_le_one (f := f) (i := i))
    _ = (n : ℝ) := by simp [Finset.card_univ, Fintype.card_fin]


lemma BooleanFourier.totalInfluence_le_n
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f ≤ (n : ℝ) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
