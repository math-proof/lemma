/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part3
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

def mex_remove_equiv {N : ℕ} (R : Multiset ℕ)
    (hpos : ∀ x ∈ R, 0 < x) (hsum : R.sum ≤ N) :
    {p : Nat.Partition N // R ≤ p.parts} ≃ Nat.Partition (N - R.sum) where
  toFun p :=
    ⟨p.1.parts - R,
      by
        intro x hi
        exact p.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
      by
        have hcancel := Multiset.sub_add_cancel p.2
        have hs := congrArg Multiset.sum hcancel
        rw [Multiset.sum_add, p.1.parts_sum] at hs
        omega⟩
  invFun q :=
    ⟨⟨q.parts + R,
      by
        intro x hx
        rw [Multiset.mem_add] at hx
        rcases hx with hx | hx
        · exact q.parts_pos hx
        · exact hpos x hx,
      by
        rw [Multiset.sum_add, q.parts_sum]
        omega⟩,
      Multiset.le_add_left R q.parts⟩
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.sub_add_cancel p.2
  right_inv q := by
    apply Nat.Partition.ext
    exact Multiset.add_sub_cancel_right

end MetaMathlibExt
