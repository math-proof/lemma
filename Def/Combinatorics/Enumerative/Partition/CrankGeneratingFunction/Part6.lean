module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part4


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

noncomputable def crkPhiFun (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) : Nat.Partition L :=
  crkMkPartition L (phiPivot (Multiset.count 1 π.parts) (nonOneParts π))
    (phiList (Multiset.count 1 π.parts) (nonOneParts π))
    (fun x hx => by
      have hge := crk_phi_ge_two _ _ (crk_nonOne_ge_two π) x hx
      omega)
    (by
      have hlen := (crk_phi_index k L hk π hπ).1
      rw [crk_phi_sum _ _ hlen]
      exact crk_omega_add_sum π)

end CrankNonneg
end MetaMathlibExt
