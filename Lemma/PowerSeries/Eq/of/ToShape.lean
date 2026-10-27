import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_eq_of_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {d1 d2 : Domino}
  (h : d1.toShape = d2.toShape) :
-- imply
  d1 = d2 := by
-- proof
  cases d1 with
  | horizontal i1 j1 =>
    cases d2 with
    | horizontal i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1 + 1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> [omega; simp only [hi1, hj1]]
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
    | vertical i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1 + 1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ <;>
      rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
  | vertical i1 j1 =>
    cases d2 with
    | horizontal i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1, j1 + 1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ <;>
      rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
    | vertical i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1, j1 + 1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> [omega; simp only [hi1, hj1]]
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega


-- created on 2026-10-20
