module

public import Def.AlgebraicGeometry_CoherentBaseChange
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Structure.AlgebraicGeometry_TwoChartCech

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech


namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

def cechDiff : S.M0 × S.M1 →ₗ[R] S.M01 := (-S.r0).coprod S.r1

abbrev H0 : Submodule R (S.M0 × S.M1) := LinearMap.ker S.cechDiff

abbrev H1 : Type w := S.M01 ⧸ LinearMap.range S.cechDiff

end Sections

namespace Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R)

@[reducible] def lineBundle (t : 𝒰.A01ˣ) : Sections.{u, v, v} 𝒰 where
  M0 := 𝒰.A0
  M1 := 𝒰.A1
  M01 := 𝒰.A01
  r0 := 𝒰.ρ0.toLinearMap
  r1 := (t : 𝒰.A01) • 𝒰.ρ1.toLinearMap
  r0_smul a m := by simp
  r1_smul a m := by simp [mul_left_comm]

abbrev structureSheaf : Sections.{u, v, v} 𝒰 := 𝒰.lineBundle 1

end Cover

section Dock

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

def kerBaseChangeHom (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker d) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  ((LinearMap.ker d).subtype.baseChange A).codRestrict (LinearMap.ker (d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : d ∘ₗ (LinearMap.ker d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

def kerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : LinearMap.ker dK →ₗ[R] LinearMap.ker d :=
  ι0.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, comm, LinearMap.comp_apply, hx, map_zero]

def cokerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : (K1 ⧸ LinearMap.range dK) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  Submodule.mapQ _ _ ι1 fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _


end Dock

def Cover.trivial (R : Type u) [CommRing R] : Cover.{u, u} R where
  A0 := R
  A1 := R
  A01 := R
  ρ0 := AlgHom.id R R
  ρ1 := AlgHom.id R R

@[reducible] def Sections.ofSubmodules {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) : Sections.{u, u, v} (Cover.trivial R) :=

  letI : Module (Cover.trivial R).A0 N0 := inferInstanceAs (Module R N0)
  letI : Module (Cover.trivial R).A1 N1 := inferInstanceAs (Module R N1)
  letI : Module (Cover.trivial R).A01 N01 := inferInstanceAs (Module R N01)
  haveI : IsScalarTower R (Cover.trivial R).A0 N0 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A1 N1 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A01 N01 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  { M0 := N0
    M1 := N1
    M01 := N01
    r0 := Submodule.inclusion h0
    r1 := Submodule.inclusion h1
    r0_smul := fun _ _ => rfl
    r1_smul := fun _ _ => rfl }


end TwoChartCech

end

end
