import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Defs

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section FiltrationPredicates

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def ToricStable (G : Type*) [Group G] [DistribMulAction G J] (𝒯 : Submodule R J) : Prop :=
  ∀ g : G, ∀ x ∈ 𝒯, g • x ∈ 𝒯

def ToricInertiaFixed (I : Subgroup G) (𝒯 : Submodule R J) : Prop :=
  ∀ σ ∈ I, ∀ x ∈ 𝒯, σ • x = x

def InertiaUnipotentTowards (I : Subgroup G) (𝒯 : Submodule R J) : Prop :=
  ∀ σ ∈ I, ∀ x : J, σ • x - x ∈ 𝒯

def IsInertiaFiltration (I : Subgroup G) (𝒯 : Submodule R J) : Prop :=
  𝒯 ≠ ⊤ ∧ ToricStable G 𝒯 ∧ ToricInertiaFixed I 𝒯 ∧ InertiaUnipotentTowards I 𝒯

end FiltrationPredicates

section ToricFrobenius

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def ToricFrobeniusSq (q : ℕ) (φ : G) (𝒯 : Submodule R J) : Prop :=
  ∀ x ∈ 𝒯, φ • φ • x = ((q : ℤ) ^ 2) • x

end ToricFrobenius

end ModularCurve

end
