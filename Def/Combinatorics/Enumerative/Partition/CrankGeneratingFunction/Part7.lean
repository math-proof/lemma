module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part5


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

noncomputable def crkPhi (k L : ℕ) (hk : 1 ≤ k)
    (π : { π : Nat.Partition L // highPartsCond k π }) :
    { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) } :=
  ⟨crkPhiFun k L hk π.1 π.2, crkPhiFun_mem k L hk π.1 π.2⟩

end CrankNonneg
end MetaMathlibExt
