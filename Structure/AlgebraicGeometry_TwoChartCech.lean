import Structure.AlgebraicGeometry_CoherentBaseChange
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech

structure Cover (R : Type u) [CommRing R] where

  A0 : Type v

  A1 : Type v

  A01 : Type v
  [A0_commRing : CommRing A0]
  [A0_algebra : Algebra R A0]
  [A1_commRing : CommRing A1]
  [A1_algebra : Algebra R A1]
  [A01_commRing : CommRing A01]
  [A01_algebra : Algebra R A01]

  ρ0 : A0 →ₐ[R] A01

  ρ1 : A1 →ₐ[R] A01

attribute [instance] Cover.A0_commRing Cover.A0_algebra Cover.A1_commRing Cover.A1_algebra
  Cover.A01_commRing Cover.A01_algebra

structure Sections {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) where

  M0 : Type w

  M1 : Type w

  M01 : Type w
  [M0_addCommGroup : AddCommGroup M0]
  [M0_moduleA : Module 𝒰.A0 M0]
  [M0_module : Module R M0]
  [M0_tower : IsScalarTower R 𝒰.A0 M0]
  [M1_addCommGroup : AddCommGroup M1]
  [M1_moduleA : Module 𝒰.A1 M1]
  [M1_module : Module R M1]
  [M1_tower : IsScalarTower R 𝒰.A1 M1]
  [M01_addCommGroup : AddCommGroup M01]
  [M01_moduleA : Module 𝒰.A01 M01]
  [M01_module : Module R M01]
  [M01_tower : IsScalarTower R 𝒰.A01 M01]

  r0 : M0 →ₗ[R] M01

  r1 : M1 →ₗ[R] M01

  r0_smul : ∀ (a : 𝒰.A0) (m : M0), r0 (a • m) = 𝒰.ρ0 a • r0 m

  r1_smul : ∀ (a : 𝒰.A1) (m : M1), r1 (a • m) = 𝒰.ρ1 a • r1 m

attribute [instance] Sections.M0_addCommGroup Sections.M0_moduleA Sections.M0_module
  Sections.M0_tower Sections.M1_addCommGroup Sections.M1_moduleA Sections.M1_module
  Sections.M1_tower Sections.M01_addCommGroup Sections.M01_moduleA Sections.M01_module
  Sections.M01_tower

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)


end Sections

namespace Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R)


end Cover

section Dock

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]


def kerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    LinearMap.ker (dK.baseChange A) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  (ι0.baseChange A).restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, comm, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx, map_zero]

def cokerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    ((A ⊗[R] K1) ⧸ LinearMap.range (dK.baseChange A)) →ₗ[A]
      ((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) :=
  Submodule.mapQ _ _ (ι1.baseChange A) fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← comm,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

structure GrothendieckComplex (d : C0 →ₗ[R] C1) where

  G : CoherentBaseChange.TwoTermComplex.{u, v} R

  ι0 : G.C0 →ₗ[R] C0

  ι1 : G.C1 →ₗ[R] C1
  comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d
  bijective_kerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (kerMapBaseChange G.d d ι0 ι1 comm A)
  bijective_cokerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (cokerMapBaseChange G.d d ι0 ι1 comm A)

end Dock


section Gates


end Gates

end TwoChartCech

end
