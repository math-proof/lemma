import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (offset : ℤ) :
-- imply
  (d.shift offset).toShape = d.toShape.image (fun p => (p.1 + offset, p.2)) := by
-- proof
  cases d with
  | horizontal i j =>
    simp only [shift, toShape, Set.image_insert_eq, Set.image_singleton]
    ext ⟨x, y⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · left; omega
      · right; omega
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · left; omega
      · right; omega
  | vertical i j =>
    simp only [shift, toShape, Set.image_insert_eq, Set.image_singleton]


-- created on 2026-10-20
