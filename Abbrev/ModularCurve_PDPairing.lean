import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Lemma.ModularCurve.PeriodMap

set_option autoImplicit false

namespace ModularCurve.PDPairing

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

section Cores
variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

end Cores

section ConjMats

variable (ℓ d : ℕ)

end ConjMats

section Gamma0Legs

variable (M M' d : ℕ)

end Gamma0Legs

section Gamma0Hecke

variable (M : ℕ)

end Gamma0Hecke

section Prim
variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]


variable [IsFreeGroup Φ]

end Prim

section Cusps

open MulAction

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {R : Type*} [CommRing R]

abbrev Cusp : Type := Quotient (orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Φ))

end Cusps

section Descent

variable (Λ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ]
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {R : Type*} [CommRing R]

end Descent

section LevelZ

open ModularCurve.Period

variable (N : ℕ) [NeZero N] [IsFreeGroup ↥(Gamma 4)]

end LevelZ

end ModularCurve.PDPairing
