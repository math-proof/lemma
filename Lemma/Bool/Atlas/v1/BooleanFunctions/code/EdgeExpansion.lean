import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.EdgeExpansion
open BooleanAnalysis


namespace BooleanAnalysis

/--
[WeightedRegularGraph.edgeExpansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma WeightedRegularGraph.edgeExpansion_empty
  [Fintype V]
  [DecidableEq V]
  {G : WeightedRegularGraph V} :
-- imply
  G.edgeExpansion ∅ = 0 := by
-- proof
  simp [WeightedRegularGraph.edgeExpansion]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[WeightedRegularGraph.edgeExpansion_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma WeightedRegularGraph.edgeExpansion_nonneg
  [Fintype V]
  [DecidableEq V]
  {G : WeightedRegularGraph V}
  {S : Finset V} :
-- imply
  0 ≤ G.edgeExpansion S := by
-- proof
  unfold WeightedRegularGraph.edgeExpansion
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro x _
      apply Finset.sum_nonneg
      intro y _
      exact G.weight_nonneg x y
    · apply mul_nonneg
      · exact le_of_lt G.degree_pos
      · exact Nat.cast_nonneg _

end BooleanAnalysis

namespace BooleanAnalysis

/--
[flip_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma flip_apply_same
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flip x i i = !x i := by
-- proof
  simp [flip]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[flip_apply_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma flip_apply_ne
  {x : Fin n → Bool}
  {i j : Fin n}
-- given
  (h : j ≠ i) :
-- imply
  flip x i j = x j := by
-- proof
  simp [flip, Function.update_of_ne h]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[flip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma flip_injective
  {x : Fin n → Bool} :
-- imply
  Function.Injective (flip x) := by
-- proof
  intro i j hij
  by_contra h_ne
  have hi : flip x i i = flip x j i := congr_fun hij i
  rw [flip_apply_same, flip_apply_ne x j i h_ne] at hi
  simp at hi

end BooleanAnalysis

namespace BooleanAnalysis

/--
[edgeExpansion_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma edgeExpansion_nonneg
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  0 ≤ edgeExpansion n A := by
-- proof
  unfold edgeExpansion
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _

end BooleanAnalysis

namespace BooleanAnalysis

/--
[edgeExpansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma edgeExpansion_empty
  {n : ℕ} :
-- imply
  edgeExpansion n (∅ : Finset (Fin n → Bool)) = 0 := by
-- proof
  simp [edgeExpansion]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[edgeBoundaryMeasure_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/EdgeExpansion.lean)
-/
@[path]
lemma edgeBoundaryMeasure_def
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
-- given
  (hn : n ≠ 0) :
-- imply
  edgeBoundaryMeasure n A = ((Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).card : ℝ) / (n * 2 ^ n : ℝ) := by
-- proof
  simp [edgeBoundaryMeasure, hn]

end BooleanAnalysis


-- created on 2026-10-23
