import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Claim32Lec8.booleanAnalysis.card_boundary_eq_sum
open BooleanAnalysis Finset Bool


/--
[edgeBoundaryMeasure_eq_totalInfluence_indicator_div_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
-- given
  (hn : n ≠ 0) :
-- imply
  edgeBoundaryMeasure n A = BooleanFourier.totalInfluence (indicator A) / (n : ℝ) := by
-- proof
  rw [edgeBoundaryMeasure_def hn, totalInfluence_indicator, div_div]
  congr 1
  ·
    have hcard := card_boundary_eq_sum (A := A)
    exact_mod_cast hcard
  · ring


lemma BooleanAnalysis.edgeBoundaryMeasure_eq_totalInfluence_indicator_div_n
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
-- given
  (hn : n ≠ 0) :
-- imply
  edgeBoundaryMeasure n A = BooleanFourier.totalInfluence (indicator A) / (n : ℝ) :=
-- proof
  main hn


-- created on 2026-10-23
-- updated on 2026-11-24
