module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part7


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

theorem crk_psi_index (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    Multiset.count 1 ν.parts ≠ 0 ∧
    psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k + 1
      ≤ Multiset.count 1 ν.parts := by
  have hN1 := crk_le_neg_impl ν (by omega : 1 ≤ k + 1) hν
  obtain ⟨-, hne⟩ := hN1
  refine ⟨hne, ?_⟩
  have hc1 : 1 ≤ Multiset.count 1 ν.parts := by omega
  have hfil : (ν.parts.filter (fun x => Multiset.count 1 ν.parts < x)).card
      = psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) :=
    crk_filter_threshold ν _ hc1
  unfold partitionCrank at hν
  split at hν
  · next hcon => exact absurd hcon hne
  · next _ =>
      rw [hfil] at hν
      omega

end CrankNonneg
end MetaMathlibExt
