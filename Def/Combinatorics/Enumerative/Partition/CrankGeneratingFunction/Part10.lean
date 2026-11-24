module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/
namespace MetaMathlibExt

namespace CrankNonneg

noncomputable def crkEquivPhiPsi (k L : ℕ) (hk : 1 ≤ k) :
    { π : Nat.Partition L // highPartsCond k π } ≃
    { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) } where
  toFun s := ⟨crkPhiFun k L hk s.1 s.2, crkPhiFun_mem k L hk s.1 s.2⟩
  invFun t := ⟨crkPsiFun k L hk t.1 t.2, crkPsiFun_mem k L hk t.1 t.2⟩
  left_inv s := by
    apply Subtype.ext
    exact crk_fun_left_inv k L hk s.1 s.2
  right_inv t := by
    apply Subtype.ext
    exact crk_fun_right_inv k L hk t.1 t.2

end CrankNonneg
end MetaMathlibExt
