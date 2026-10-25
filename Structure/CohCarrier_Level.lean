import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.Algebra.Module.Hom
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Instance.CohCarrier_Level

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier

section TransferAdd

variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

open Subgroup Subgroup.leftTransversals in

open Subgroup Subgroup.leftTransversals in


end TransferAdd

section Level

variable (M : ℕ)


variable {M}


end Level

section Carrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type*) [AddCommGroup A]


end Carrier

section Operators

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)


variable (A : Type*) [AddCommGroup A]


end Operators

section LevelMaps

variable (M M' : ℕ) (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ) (d : ℕ)


structure LevelLE : Prop where
  dvd : M ∣ M'
  ddvd : d ∣ M' / M
  red : ∀ u : (ZMod M')ˣ, u ∈ H' → ZMod.unitsMap dvd u ∈ H

variable {M M' H H' d}


variable (M M' H H' d)


variable (A : Type*) [AddCommGroup A]


end LevelMaps

end CohCarrier
