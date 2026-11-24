import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion.booleanAnalysis.edgeExpansion_empty
open BooleanAnalysis Bool


/--
[edgeBoundaryMeasure_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
-- given
  (hn : n ≠ 0) :
-- imply
  edgeBoundaryMeasure n A = ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => (p.1 ∈ A ∧ BooleanAnalysis.flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ BooleanAnalysis.flip p.1 p.2 ∈ A))).card : ℝ) / (n * 2 ^ n : ℝ) := by
-- proof
  simp [edgeBoundaryMeasure, hn]


lemma BooleanAnalysis.edgeBoundaryMeasure_def
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
-- given
  (hn : n ≠ 0) :
-- imply
  edgeBoundaryMeasure n A = ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => (p.1 ∈ A ∧ BooleanAnalysis.flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ BooleanAnalysis.flip p.1 p.2 ∈ A))).card : ℝ) / (n * 2 ^ n : ℝ) :=
-- proof
  main hn


-- created on 2026-10-23
-- updated on 2026-11-24
