module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part7


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

noncomputable def crkPsi (k L : ℕ) (hk : 1 ≤ k)
    (ν : { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) }) :
    { π : Nat.Partition L // highPartsCond k π } :=
  ⟨crkPsiFun k L hk ν.1 ν.2, crkPsiFun_mem k L hk ν.1 ν.2⟩

end CrankNonneg
end MetaMathlibExt
