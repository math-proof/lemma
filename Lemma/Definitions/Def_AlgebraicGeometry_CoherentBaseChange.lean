import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange

structure TwoTermComplex (R : Type u) [CommRing R] where

  C0 : Type v
  [C0_addCommGroup : AddCommGroup C0]
  [C0_module : Module R C0]
  [C0_finite : Module.Finite R C0]
  [C0_free : Module.Free R C0]

  C1 : Type v
  [C1_addCommGroup : AddCommGroup C1]
  [C1_module : Module R C1]
  [C1_finite : Module.Finite R C1]
  [C1_free : Module.Free R C1]

  d : C0 →ₗ[R] C1

attribute [instance] TwoTermComplex.C0_addCommGroup TwoTermComplex.C0_module
  TwoTermComplex.C0_finite TwoTermComplex.C0_free TwoTermComplex.C1_addCommGroup
  TwoTermComplex.C1_module TwoTermComplex.C1_finite TwoTermComplex.C1_free

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

def fibreH0 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    (LinearMap.ker (G.d.baseChange 𝔭.asIdeal.ResidueField))

def fibreH1 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    ((𝔭.asIdeal.ResidueField ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange 𝔭.asIdeal.ResidueField))

def chi : ℤ :=
  (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)

abbrev H0 (A : Type w) [CommRing A] [Algebra R A] : Submodule A (A ⊗[R] G.C0) :=
  LinearMap.ker (G.d.baseChange A)

def kerBaseChangeHom (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker G.d) →ₗ[A] G.H0 A :=
  ((LinearMap.ker G.d).subtype.baseChange A).codRestrict (LinearMap.ker (G.d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : G.d ∘ₗ (LinearMap.ker G.d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

theorem kerBaseChangeHom_apply_coe (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker G.d)) :
    (G.kerBaseChangeHom A x : A ⊗[R] G.C0) = (LinearMap.ker G.d).subtype.baseChange A x :=
  rfl

end TwoTermComplex

end CoherentBaseChange
