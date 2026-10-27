import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[dominos_eq_left_union_shifted_right_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (k : ℕ)
  (hk : hasFault n T k) :
-- imply
  T.dominos = (restrictTilingLeft n T k hk).dominos ∪
    ((restrictTilingRight n T k hk).dominos.image (fun d => d.shiftNat k)) := by
-- proof
  ext d
  simp only [Set.mem_union, Set.mem_image]
  simp only [restrictTilingLeft, restrictTilingRight, Set.mem_sep_iff, Set.mem_image]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right
      -- d is in right part, so d.shiftNeg k is in restrictTilingRight
      -- and (d.shiftNeg k).shiftNat k = d
      refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
      exact d.shiftNat_shiftNeg k
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨d', ⟨d'', ⟨hd'', _⟩, hd'_eq⟩, hd_eq⟩
    · exact hd
    · -- d = d'.shiftNat k where d' = d''.shiftNeg k and d'' ∈ T.dominos
      subst hd'_eq hd_eq
      rw [Domino.shiftNat_shiftNeg]
      exact hd''


-- created on 2026-10-20
