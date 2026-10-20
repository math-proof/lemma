import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.Overpartition
open Nat
open Overpartition


/--
[isOverlined_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma isOverlined_iff_eq
  {n : ℕ}
  {O : Overpartition n}
  {a : ℕ} :
-- imply
  O.IsOverlined a ↔ a ∈ O.overlines := by
-- proof
  apply Nat.Overpartition.isOverlined_iff

/--
[isOverlined_mem_parts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma isOverlined_mem_parts_eq
  {n : ℕ}
  {O : Overpartition n}
  {a : ℕ}
-- given
  (h : O.IsOverlined a) :
-- imply
  a ∈ O.toPartition.parts := by
-- proof
  apply Nat.Overpartition.isOverlined_mem_parts h

/--
[isOverlined_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma isOverlined_pos_eq
  {n : ℕ}
  {O : Overpartition n}
  {a : ℕ}
-- given
  (h : O.IsOverlined a) :
-- imply
  0 < a := by
-- proof
  apply Nat.Overpartition.isOverlined_pos h

/--
[ofPartition_toPartition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma ofPartition_toPartition_eq
  {n : ℕ}
  {p : Partition n} :
-- imply
  (ofPartition p).toPartition = p := by
-- proof
  apply Nat.Overpartition.ofPartition_toPartition p

/--
[ofPartition_overlines](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma ofPartition_overlines_eq
  {n : ℕ}
  {p : Partition n} :
-- imply
  (ofPartition p).overlines = ∅ := by
-- proof
  apply Nat.Overpartition.ofPartition_overlines p

/--
[not_isOverlined_ofPartition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma not_isOverlined_ofPartition_eq
  {n : ℕ}
  {p : Partition n}
  {a : ℕ} :
-- imply
  ¬ (ofPartition p).IsOverlined a := by
-- proof
  apply Nat.Overpartition.not_isOverlined_ofPartition p a

/--
[full_toPartition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma full_toPartition_eq
  {n : ℕ}
  {p : Partition n} :
-- imply
  (full p).toPartition = p := by
-- proof
  apply Nat.Overpartition.full_toPartition p

/--
[full_overlines](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma full_overlines_eq
  {n : ℕ}
  {p : Partition n} :
-- imply
  (full p).overlines = p.parts.toFinset := by
-- proof
  apply Nat.Overpartition.full_overlines p

/--
[isOverlined_full](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma isOverlined_full_eq
  {n : ℕ}
  {p : Partition n}
  {a : ℕ} :
-- imply
  (full p).IsOverlined a ↔ a ∈ p.parts := by
-- proof
  apply Nat.Overpartition.isOverlined_full p a

/--
[overlines_eq_empty_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma overlines_eq_empty_of_zero_eq
  {O : Overpartition 0} :
-- imply
  O.overlines = ∅ := by
-- proof
  apply Nat.Overpartition.overlines_eq_empty_of_zero

/--
[eq_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
private lemma eq_of_zero_eq
  {O₁ O₂ : Overpartition 0} :
-- imply
  O₁ = O₂ := by
-- proof
  apply Nat.Overpartition.eq_of_zero O₁ O₂


-- created on 2026-10-20
