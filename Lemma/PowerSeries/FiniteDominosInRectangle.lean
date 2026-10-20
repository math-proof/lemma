import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[dominos_in_rectangle_finite_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n m : ℕ) :
-- imply
  Set.Finite (DominosInRectangle n m) := by
-- proof
  have h : DominosInRectangle n m ⊆
      (Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m).image (fun p => Domino.horizontal p.1 p.2) ∪
      (Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m).image (fun p => Domino.vertical p.1 p.2) := by
    intro d hd
    cases d with
    | horizontal i j =>
      left
      simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
      use (i, j)
      simp only [DominosInRectangle, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
      have h1 := hd (i, j) (by simp)
      simp only [Rectangle, Set.mem_ofPred_eq] at h1
      refine ⟨⟨⟨h1.1, ?_⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩, rfl⟩
      omega
    | vertical i j =>
      right
      simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
      use (i, j)
      simp only [DominosInRectangle, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
      have h1 := hd (i, j) (by simp)
      simp only [Rectangle, Set.mem_ofPred_eq] at h1
      refine ⟨⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, ?_⟩⟩, rfl⟩
      omega
  apply Set.Finite.subset _ h
  apply Set.Finite.union
  · apply Set.Finite.image
    apply Set.Finite.prod
    · exact Set.finite_Icc (1 : ℤ) n
    · exact Set.finite_Icc (1 : ℤ) m
  · apply Set.Finite.image
    apply Set.Finite.prod
    · exact Set.finite_Icc (1 : ℤ) n
    · exact Set.finite_Icc (1 : ℤ) m


-- created on 2026-10-20
