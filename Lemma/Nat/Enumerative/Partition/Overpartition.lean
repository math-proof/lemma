import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.Overpartition
open Nat
open Overpartition


namespace Nat.Overpartition

/--
[isOverlined_full](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma isOverlined_full
  {n : ℕ}
  {p : Partition n}
  {a : ℕ} :
-- imply
  (full p).IsOverlined a ↔ a ∈ p.parts := by
-- proof
  simp [IsOverlined]

end Nat.Overpartition

namespace Nat.Overpartition

/--
[overlines_eq_empty_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma overlines_eq_empty_of_zero
  {O : Overpartition 0} :
-- imply
  O.overlines = ∅ := by
-- proof
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have h := O.overlines_subset ha
  rw [Partition.partition_zero_parts] at h
  simp at h

end Nat.Overpartition

namespace Nat.Overpartition

/--
[eq_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma eq_of_zero
  {O₁ O₂ : Overpartition 0} :
-- imply
  O₁ = O₂ := by
-- proof
  apply Overpartition.ext
  · exact Subsingleton.elim _ _
  · rw [overlines_eq_empty_of_zero (O := O₁), overlines_eq_empty_of_zero (O := O₂)]

end Nat.Overpartition

/--
[isOverlined_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma isOverlined_iff
  {n : ℕ}
  {O : Overpartition n}
  {a : ℕ} :
-- imply
  O.IsOverlined a ↔ a ∈ O.overlines :=
-- proof
  Iff.rfl


namespace Nat.Overpartition

/--
[isOverlined_mem_parts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma isOverlined_mem_parts
  {n : ℕ}
  {O : Overpartition n}
  {a : ℕ}
-- given
  (h : O.IsOverlined a) :
-- imply
  a ∈ O.toPartition.parts :=
-- proof
  Multiset.mem_toFinset.mp (O.overlines_subset h)

end Nat.Overpartition

namespace Nat.Overpartition

/--
[isOverlined_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma isOverlined_pos
  {n : ℕ}
  {O : Overpartition n}
  {a : ℕ}
-- given
  (h : O.IsOverlined a) :
-- imply
  0 < a :=
-- proof
  O.toPartition.parts_pos (isOverlined_mem_parts h)

end Nat.Overpartition

namespace Nat.Overpartition

/--
[ofPartition_toPartition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma ofPartition_toPartition
  {n : ℕ}
  {p : Partition n} :
-- imply
  (ofPartition p).toPartition = p :=
-- proof
  rfl

end Nat.Overpartition

namespace Nat.Overpartition

/--
[ofPartition_overlines](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma ofPartition_overlines
  {n : ℕ}
  {p : Partition n} :
-- imply
  (ofPartition p).overlines = ∅ :=
-- proof
  rfl

end Nat.Overpartition

namespace Nat.Overpartition

/--
[not_isOverlined_ofPartition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma not_isOverlined_ofPartition
  {n : ℕ}
  {p : Partition n}
  {a : ℕ} :
-- imply
  ¬ (ofPartition p).IsOverlined a := by
-- proof
  simp [IsOverlined]

end Nat.Overpartition

namespace Nat.Overpartition

/--
[full_toPartition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma full_toPartition
  {n : ℕ}
  {p : Partition n} :
-- imply
  (full p).toPartition = p :=
-- proof
  rfl

end Nat.Overpartition

namespace Nat.Overpartition

/--
[full_overlines](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean)
-/
@[path]
lemma full_overlines
  {n : ℕ}
  {p : Partition n} :
-- imply
  (full p).overlines = p.parts.toFinset :=
-- proof
  rfl

end Nat.Overpartition


-- created on 2026-10-20
-- updated on 2026-10-23
