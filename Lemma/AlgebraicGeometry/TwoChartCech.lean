import Def.AlgebraicGeometry_CoherentBaseChange
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Structure.AlgebraicGeometry_TwoChartCech

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech


namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

def cechDiff : S.M0 × S.M1 →ₗ[R] S.M01 := (-S.r0).coprod S.r1

theorem cechDiff_apply (s : S.M0 × S.M1) : S.cechDiff s = S.r1 s.2 - S.r0 s.1 := by
  simp [cechDiff, LinearMap.coprod_apply, sub_eq_neg_add]

abbrev H0 : Submodule R (S.M0 × S.M1) := LinearMap.ker S.cechDiff

theorem mem_H0_iff (s : S.M0 × S.M1) : s ∈ S.H0 ↔ S.r0 s.1 = S.r1 s.2 := by
  rw [LinearMap.mem_ker, cechDiff_apply, sub_eq_zero, eq_comm]

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

@[simp] theorem lineBundle_r0_apply (t : 𝒰.A01ˣ) (p : 𝒰.A0) : (𝒰.lineBundle t).r0 p = 𝒰.ρ0 p := rfl
@[simp] theorem lineBundle_r1_apply (t : 𝒰.A01ˣ) (p : 𝒰.A1) :
    (𝒰.lineBundle t).r1 p = (t : 𝒰.A01) * 𝒰.ρ1 p := rfl

theorem mem_H0_lineBundle_iff (t : 𝒰.A01ˣ) (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ (𝒰.lineBundle t).H0 ↔ 𝒰.ρ0 p.1 = (t : 𝒰.A01) * 𝒰.ρ1 p.2 :=
  (𝒰.lineBundle t).mem_H0_iff p

abbrev structureSheaf : Sections.{u, v, v} 𝒰 := 𝒰.lineBundle 1

theorem mem_H0_structureSheaf_iff (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ 𝒰.structureSheaf.H0 ↔ 𝒰.ρ0 p.1 = 𝒰.ρ1 p.2 := by
  rw [mem_H0_lineBundle_iff, Units.val_one, one_mul]

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

theorem kerBaseChangeHom_apply_coe (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker d)) :
    (kerBaseChangeHom d A x : A ⊗[R] C0) = (LinearMap.ker d).subtype.baseChange A x :=
  rfl

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

theorem Sections.mem_H0_ofSubmodules_iff {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F]
    [Module R F] (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) (p : N0 × N1) :
    p ∈ (Sections.ofSubmodules N0 N1 N01 h0 h1).H0 ↔ (p.1 : F) = p.2 :=
  ((Sections.ofSubmodules N0 N1 N01 h0 h1).mem_H0_iff p).trans
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

section Gates

example (R : Type u) [CommRing R] (a b : R) :
    (a, b) ∈ (Cover.trivial R).structureSheaf.H0 ↔ a = b :=
  (Cover.trivial R).mem_H0_structureSheaf_iff (a, b)

example : ((1 : (Cover.trivial ℤ).A0), (1 : (Cover.trivial ℤ).A1)) ∉ ((Cover.trivial ℤ).lineBundle (-1)).H0 := by
  rw [Cover.mem_H0_lineBundle_iff]
  change ¬ ((1 : ℤ) = (-1 : ℤ) * 1)
  decide

example : ((1 : (Cover.trivial ℤ).A0), (-1 : (Cover.trivial ℤ).A1)) ∈ ((Cover.trivial ℤ).lineBundle (-1)).H0 := by
  rw [Cover.mem_H0_lineBundle_iff]
  change ((1 : ℤ) = (-1 : ℤ) * -1)
  decide

example (R : Type u) [CommRing R] : GrothendieckComplex (0 : R →ₗ[R] R) where
  G := { C0 := R, C1 := R, d := 0 }
  ι0 := LinearMap.id
  ι1 := LinearMap.id
  comm := by simp
  bijective_kerMap A _ _ := by
    have h : ∀ x, (kerMapBaseChange (0 : R →ₗ[R] R) 0 LinearMap.id LinearMap.id (by simp) A x) = x :=
      fun x => Subtype.ext (by simp [kerMapBaseChange, LinearMap.restrict_apply])
    exact ⟨fun x y hxy => by rwa [h, h] at hxy, fun y => ⟨y, h y⟩⟩
  bijective_cokerMap A _ _ := by
    have h : ∀ z, cokerMapBaseChange (0 : R →ₗ[R] R) 0 LinearMap.id LinearMap.id (by simp) A z = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        show Submodule.Quotient.mk ((LinearMap.id.baseChange A) z) = Submodule.Quotient.mk z
        rw [LinearMap.baseChange_id, LinearMap.id_apply]
    exact ⟨fun x y hxy => by rwa [h, h] at hxy, fun y => ⟨y, h y⟩⟩

end Gates

end TwoChartCech

end
