/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction

@[expose] public section

namespace MetaMathlibExt

namespace CrankNonneg

instance crkDecHigh (k : ℕ) {L : ℕ} :
    DecidablePred (highPartsCond k : Nat.Partition L → Prop) :=
  fun π => by unfold highPartsCond; infer_instance

end CrankNonneg
end MetaMathlibExt
