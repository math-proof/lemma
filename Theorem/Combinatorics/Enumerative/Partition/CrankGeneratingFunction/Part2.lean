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
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part3


namespace MetaMathlibExt

namespace CrankNonneg

theorem crkAddOnes_parts (k L : ℕ) (π : Nat.Partition L) :
    (crkAddOnes k L π).1.parts = π.parts + Multiset.replicate k 1 :=
  rfl

theorem crkAddOnes_omega (k L : ℕ) (π : Nat.Partition L) :
    Multiset.count 1 (crkAddOnes k L π).1.parts = Multiset.count 1 π.parts + k := by
  rw [crkAddOnes_parts, Multiset.count_add, Multiset.count_replicate_self]

/-! ## Crank of the add-ones image -/

theorem crk_addOnes_filter (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L) :
    ((crkAddOnes k L π).1.parts.filter
      (fun x => Multiset.count 1 π.parts + k < x)).card =
    (π.parts.filter (fun x => Multiset.count 1 π.parts + k < x)).card := by
  rw [crkAddOnes_parts, Multiset.filter_add, Multiset.card_add]
  have hrep : (Multiset.replicate k 1).filter
      (fun x => Multiset.count 1 π.parts + k < x) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_replicate] at hx
    obtain ⟨-, rfl⟩ := hx
    omega
  rw [hrep, Multiset.card_zero, Nat.add_zero]

theorem crk_addOnes_crank (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L) :
    partitionCrank (crkAddOnes k L π).1 =
      ((π.parts.filter (fun x => Multiset.count 1 π.parts + k < x)).card : ℤ) -
      ((Multiset.count 1 π.parts + k : ℕ) : ℤ) := by
  have hQ : Multiset.count 1 (crkAddOnes k L π).1.parts =
      Multiset.count 1 π.parts + k :=
    crkAddOnes_omega k L π
  have hne : Multiset.count 1 (crkAddOnes k L π).1.parts ≠ 0 := by omega
  unfold partitionCrank
  split
  · next hcon => exact absurd hcon hne
  · next _ =>
      rw [hQ, crk_addOnes_filter k L hk π]

theorem crk_not_le_iff_highParts (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L) :
    ¬ partitionCrank (crkAddOnes k L π).1 ≤ -(k : ℤ) ↔ highPartsCond k π := by
  rw [crk_addOnes_crank k L hk π]
  unfold highPartsCond
  constructor <;> intro h <;> omega

end CrankNonneg
end MetaMathlibExt
