/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction


namespace MetaMathlibExt

namespace CrankNonneg

/-! ## Adding `k` ones -/

noncomputable def crkAddOnes (k L : ℕ) :
    Nat.Partition L ≃ { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } where
  toFun π :=
    ⟨⟨π.parts + Multiset.replicate k 1,
      by
        intro i hi
        rw [Multiset.mem_add] at hi
        rcases hi with h | h
        · exact π.parts_pos h
        · rw [Multiset.mem_replicate] at h
          obtain ⟨-, rfl⟩ := h
          exact Nat.one_pos,
      by
        rw [Multiset.sum_add, Multiset.sum_replicate, π.parts_sum, nsmul_eq_mul,
          mul_one, Nat.cast_id]⟩,
    by
      change k ≤ Multiset.count 1 (π.parts + Multiset.replicate k 1)
      rw [Multiset.count_add, Multiset.count_replicate_self]
      exact Nat.le_add_left k _⟩
  invFun Q :=
    ⟨(Q.1.parts - Multiset.replicate k 1),
      by
        intro i hi
        have hle : Multiset.replicate k 1 ≤ Q.1.parts :=
          Multiset.le_count_iff_replicate_le.mp Q.2
        exact Q.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
      by
        have hle : Multiset.replicate k 1 ≤ Q.1.parts :=
          Multiset.le_count_iff_replicate_le.mp Q.2
        have hcan := Multiset.sub_add_cancel hle
        have hs := congrArg Multiset.sum hcan
        rw [Multiset.sum_add, Multiset.sum_replicate, Q.1.parts_sum, nsmul_eq_mul,
          mul_one, Nat.cast_id] at hs
        omega⟩
  left_inv π := by
    apply Nat.Partition.ext
    change (π.parts + Multiset.replicate k 1) - Multiset.replicate k 1 = π.parts
    exact Multiset.add_sub_cancel_right
  right_inv Q := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change (Q.1.parts - Multiset.replicate k 1) + Multiset.replicate k 1 = Q.1.parts
    exact Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp Q.2)

end CrankNonneg
end MetaMathlibExt
