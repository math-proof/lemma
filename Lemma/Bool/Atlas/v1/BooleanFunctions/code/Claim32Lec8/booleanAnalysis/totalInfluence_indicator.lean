import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Claim32Lec8.booleanAnalysis.flipCoord_eq_flip
open BooleanAnalysis Finset Bool


/--
[totalInfluence_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  BooleanFourier.totalInfluence (indicator A) = (∑ i : Fin n, ((Finset.univ.filter (fun x : Fin n → Bool => (x ∈ A ∧ BooleanAnalysis.flip x i ∉ A) ∨ (x ∉ A ∧ BooleanAnalysis.flip x i ∈ A))).card : ℝ)) / (2 ^ n : ℝ) := by
-- proof
  unfold BooleanFourier.totalInfluence BooleanFourier.influence
  simp_rw [flipCoord_eq_flip, indicator_ne_iff]
  rw [← Finset.sum_div]


lemma BooleanAnalysis.totalInfluence_indicator
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  BooleanFourier.totalInfluence (indicator A) = (∑ i : Fin n, ((Finset.univ.filter (fun x : Fin n → Bool => (x ∈ A ∧ BooleanAnalysis.flip x i ∉ A) ∨ (x ∉ A ∧ BooleanAnalysis.flip x i ∈ A))).card : ℝ)) / (2 ^ n : ℝ) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
