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
import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part8


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
