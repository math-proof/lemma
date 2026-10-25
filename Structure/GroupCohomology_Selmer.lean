import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open CategoryTheory Module

universe u

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]


end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]


end Rep

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable abbrev locRes (v : ι) : H1 M ⟶ H1 (Rep.res (loc v) M) :=
  map (loc v) (𝟙 (Rep.res (loc v) M)) 1

noncomputable def selmer (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Submodule k (H1 M) :=
  ⨅ v, (L v).comap (locRes loc M v).hom

omit [Fintype ι] in


def orthogonal {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (B : V →ₗ[k] W →ₗ[k] k) (L : Submodule k V) : Submodule k W :=
  L.dualAnnihilator.comap B.flip

@[simp]


variable (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

noncomputable def dualConditions (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (v : ι) :
    Submodule k (H1 (Rep.res (loc v) M')) :=
  orthogonal (pairing v) (L v)

def greenbergWilesEq (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  finrank k (selmer loc M L)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    = finrank k (selmer loc M' (dualConditions loc M M' pairing L))
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

structure IsGreenbergWilesDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  formula : greenbergWilesEq loc M M' pairing L


end groupCohomology
