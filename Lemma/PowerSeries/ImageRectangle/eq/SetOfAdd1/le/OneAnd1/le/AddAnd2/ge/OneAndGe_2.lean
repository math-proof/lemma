import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[rectangle_shift_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n m : ℕ)
  (offset : ℤ) :
-- imply
  (Rectangle n m).image (fun p => (p.1 + offset, p.2)) =
      {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := by
-- proof
  ext ⟨x, y⟩
  simp only [Set.mem_image, Rectangle, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, ⟨h1, h2, h3, h4⟩, hx, hy⟩
    subst hx hy
    exact ⟨by omega, by omega, h3, h4⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(x - offset, y), ⟨by omega, by omega, h3, h4⟩, by omega, rfl⟩


-- created on 2026-10-20
