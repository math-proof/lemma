import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.flip_injective
open BooleanAnalysis Bool


/--
[edgeExpansion_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  0 ≤ edgeExpansion n A := by
-- proof
  unfold edgeExpansion
  split_ifs with h
  · exact le_refl 0
  ·
    apply div_nonneg
    ·
      exact Nat.cast_nonneg _
    ·
      apply mul_nonneg
      ·
        exact Nat.cast_nonneg _
      ·
        exact Nat.cast_nonneg _


lemma BooleanAnalysis.edgeExpansion_nonneg
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  0 ≤ edgeExpansion n A := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
