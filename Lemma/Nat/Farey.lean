import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Farey
open scoped Rat
open Farey


/--
[mem_fareyFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma mem_fareyFinset_iff_eq
  {n : ℕ}
  {q : ℚ} :
-- imply
  q ∈ fareyFinset n ↔ 0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n := by
-- proof
  apply Farey.mem_fareyFinset_iff n q

/--
[fareyFinset_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma fareyFinset_mono_eq
  {m n : ℕ}
-- given
  (hmn : m ≤ n) :
-- imply
  fareyFinset m ⊆ fareyFinset n := by
-- proof
  apply Farey.fareyFinset_mono hmn

/--
[det_one_and_sum_gt_imp_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma det_one_and_sum_gt_imp_neighbor_eq
  {n : ℕ}
  {x y : ℚ}
-- given
  (hx : x ∈ fareyFinset n)
  (hy : y ∈ fareyFinset n)
  (hdet : y.num * (x.den : ℤ) = x.num * (y.den : ℤ) + 1)
  (hsum : n < x.den + y.den) :
-- imply
  IsFareyNeighbor n x y := by
-- proof
  apply Farey.det_one_and_sum_gt_imp_neighbor n x y hx hy hdet hsum

/--
[IsFareyNeighbor.det_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma IsFareyNeighbor_det_eq_one_eq
  {n : ℕ}
  {x y : ℚ}
-- given
  (h : IsFareyNeighbor n x y) :
-- imply
  y.num * (x.den : ℤ) = x.num * (y.den : ℤ) + 1 := by
-- proof
  apply Farey.IsFareyNeighbor.det_eq_one h

/--
[isFareyNeighbor_iff_det_and_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma isFareyNeighbor_iff_det_and_sum_eq
  {n : ℕ}
  {x y : ℚ}
-- given
  (hx : x ∈ fareyFinset n)
  (hy : y ∈ fareyFinset n) :
-- imply
  IsFareyNeighbor n x y ↔
    y.num * (x.den : ℤ) = x.num * (y.den : ℤ) + 1 ∧ n < x.den + y.den := by
-- proof
  apply Farey.isFareyNeighbor_iff_det_and_sum hx hy

/--
[IsFareyNeighbor.mediant_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma IsFareyNeighbor_mediant_not_mem_eq
  {n : ℕ}
  {x y : ℚ}
-- given
  (h : IsFareyNeighbor n x y) :
-- imply
  mediant x y ∉ fareyFinset n := by
-- proof
  apply Farey.IsFareyNeighbor.mediant_not_mem h

/--
[IsFareyNeighbor.mediant_mem_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma IsFareyNeighbor_mediant_mem_succ_eq
  {n : ℕ}
  {x y : ℚ}
-- given
  (h : IsFareyNeighbor n x y)
  (hsum : x.den + y.den = n + 1) :
-- imply
  mediant x y ∈ fareyFinset (n + 1) ∧ mediant x y ∉ fareyFinset n := by
-- proof
  apply Farey.IsFareyNeighbor.mediant_mem_succ h hsum

/--
[farey_succ_generation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean)
-/
@[path]
private lemma farey_succ_generation_eq
  {n : ℕ}
  {q : ℚ}
-- given
  (hn : 0 < n) :
-- imply
  q ∈ fareyFinset (n + 1) ↔
    q ∈ fareyFinset n ∨
    ∃ x y : ℚ, IsFareyNeighbor n x y ∧ x.den + y.den = n + 1 ∧ q = mediant x y := by
-- proof
  apply Farey.farey_succ_generation hn q


-- created on 2026-10-20
