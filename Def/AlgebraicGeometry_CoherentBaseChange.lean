import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Structure.AlgebraicGeometry_CoherentBaseChange
import Abbrev.AlgebraicGeometry_CoherentBaseChange

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange


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
