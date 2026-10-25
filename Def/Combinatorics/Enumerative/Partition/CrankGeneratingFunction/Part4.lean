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
import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part2


namespace MetaMathlibExt

namespace CrankNonneg

/-! ## Recursion first half -/

def crkEquivLe (k L : ℕ) (hk : 1 ≤ k) :
    { s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } //
      partitionCrank s.1 ≤ -(k : ℤ) } ≃
    { Q : Nat.Partition (L + k) // partitionCrank Q ≤ -(k : ℤ) } :=
  Equiv.subtypeSubtypeEquivSubtype (fun hQ => (crk_le_neg_impl _ hk hQ).1)

noncomputable def crkEquivHigh (k L : ℕ) (hk : 1 ≤ k) :
    { s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } //
      ¬ partitionCrank s.1 ≤ -(k : ℤ) } ≃
    { π : Nat.Partition L // highPartsCond k π } where
  toFun s :=
    ⟨(crkAddOnes k L).symm s.1,
    by
      have h1 : ((crkAddOnes k L) ((crkAddOnes k L).symm s.1)).1 =
          (s.1 : Nat.Partition (L + k)) :=
        congrArg Subtype.val (Equiv.apply_symm_apply _ _)
      have h2 : ¬ partitionCrank
          ((crkAddOnes k L) ((crkAddOnes k L).symm s.1)).1 ≤ -(k : ℤ) := by
        rw [h1]
        exact s.2
      exact (crk_not_le_iff_highParts k L hk _).mp h2⟩
  invFun t :=
    ⟨(crkAddOnes k L) t.1,
    by
      exact (crk_not_le_iff_highParts k L hk t.1).mpr t.2⟩
  left_inv s := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply _ _
  right_inv t := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply _ _

end CrankNonneg
end MetaMathlibExt
