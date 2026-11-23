module

public import Def.AlgebraicGeometry_CoherentBaseChange
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Structure.AlgebraicGeometry_TwoChartCech

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech


namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)


public theorem cechDiff_apply (s : S.M0 × S.M1) : S.cechDiff s = S.r1 s.2 - S.r0 s.1 := by
  simp [cechDiff, LinearMap.coprod_apply, sub_eq_neg_add]


public theorem mem_H0_iff (s : S.M0 × S.M1) : s ∈ S.H0 ↔ S.r0 s.1 = S.r1 s.2 := by
  rw [LinearMap.mem_ker, cechDiff_apply, sub_eq_zero, eq_comm]


@[simp] public theorem lineBundle_r0_apply (t : 𝒰.A01ˣ) (p : 𝒰.A0) : (𝒰.lineBundle t).r0 p = 𝒰.ρ0 p := rfl

@[simp] public theorem lineBundle_r1_apply (t : 𝒰.A01ˣ) (p : 𝒰.A1) :
    (𝒰.lineBundle t).r1 p = (t : 𝒰.A01) * 𝒰.ρ1 p := rfl


public theorem mem_H0_lineBundle_iff (t : 𝒰.A01ˣ) (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ (𝒰.lineBundle t).H0 ↔ 𝒰.ρ0 p.1 = (t : 𝒰.A01) * 𝒰.ρ1 p.2 :=
  (𝒰.lineBundle t).mem_H0_iff p


public theorem mem_H0_structureSheaf_iff (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ 𝒰.structureSheaf.H0 ↔ 𝒰.ρ0 p.1 = 𝒰.ρ1 p.2 := by
  rw [mem_H0_lineBundle_iff, Units.val_one, one_mul]

end Cover

section Dock

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]


public theorem kerBaseChangeHom_apply_coe (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker d)) :
    (kerBaseChangeHom d A x : A ⊗[R] C0) = (LinearMap.ker d).subtype.baseChange A x :=
  rfl


public theorem Sections.mem_H0_ofSubmodules_iff {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F]
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
