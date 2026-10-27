import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


/--
[domino_left_or_right_at_fault_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {n : ℕ}
  {T : Tiling (Rectangle n 2)}
  {k : ℕ}
  (d : Domino)
  (hk : hasFault n T k)
  (hd : d ∈ T.dominos) :
-- imply
  d.inLeftPart k ∨ d.inRightPart k := by
-- proof
  cases d with
  | horizontal i j =>
    have hfault := hk.2.2 (Domino.horizontal i j) hd
    simp only [Domino.inLeftPart, Domino.inRightPart, Domino.toShape]
    rcases hfault with hlt | hge
    · left
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
    · right
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
  | vertical i j =>
    simp only [Domino.inLeftPart, Domino.inRightPart, Domino.toShape]
    -- Get x-coordinate bound from the domino being in the tiling
    have hsub := domino_subset_rect n T (Domino.vertical i j) hd
    have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
    simp only [Rectangle, Set.mem_ofPred_eq] at h1
    by_cases hi : i ≤ k
    · left
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
    · right
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega


-- created on 2026-10-20
