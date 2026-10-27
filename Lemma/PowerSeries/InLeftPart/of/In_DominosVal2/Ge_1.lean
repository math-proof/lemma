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
[compose_tilings_component0_in_left_part_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (d : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 1)
  (hd : d ∈ (ts ⟨0, hk⟩).2.val.dominos) :
-- imply
  d.inLeftPart (ts ⟨0, hk⟩).1 := by
-- proof
  intro p hp
  have hsub := domino_subset_rect (ts ⟨0, hk⟩).1 (ts ⟨0, hk⟩).2.val d hd
  have hp_rect := hsub hp
  simp only [Rectangle, Set.mem_ofPred_eq] at hp_rect
  exact hp_rect.2.1


-- created on 2026-10-20
