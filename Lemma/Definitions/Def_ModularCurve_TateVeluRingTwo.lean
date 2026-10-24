import Mathlib
import Lemma.Definitions.Def_ModularCurve_TateVeluRing
import Lemma.Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Lemma.Definitions.Def_WeierstrassCurve_VeluPointMap2

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve

namespace ModularCurve.TateVeluRing

section Velu2R

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A)

noncomputable def velu2XR (x₀ y₀ x : A) : A := x + W.veluGx x₀ y₀ * Ring.inverse (x - x₀)

noncomputable def velu2YR (x₀ y₀ x y : A) : A :=
  y - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * Ring.inverse (x - x₀) ^ 2

theorem velu2XR_eq_velu2X {F : Type*} [Field F] (W : WeierstrassCurve F) (x₀ y₀ x : F) :
    velu2XR W x₀ y₀ x = W.velu2X x₀ y₀ x := by
  unfold velu2XR WeierstrassCurve.velu2X
  simp only [Ring.inverse_eq_inv', div_eq_mul_inv]

theorem velu2YR_eq_velu2Y {F : Type*} [Field F] (W : WeierstrassCurve F) (x₀ y₀ x y : F) :
    velu2YR W x₀ y₀ x y = W.velu2Y x₀ y₀ x y := by
  unfold velu2YR WeierstrassCurve.velu2Y
  simp only [Ring.inverse_eq_inv', div_eq_mul_inv, inv_pow]

variable {B : Type*} [CommRing B] (f : A →+* B)

theorem map_velu2XR (x₀ y₀ x : A) (hunit : IsUnit (x - x₀)) :
    f (velu2XR W x₀ y₀ x) = velu2XR (W.map f) (f x₀) (f y₀) (f x) := by
  unfold velu2XR
  have h := map_ringInverse_of_isUnit f hunit
  rw [map_sub] at h
  simp only [map_veluGx, map_add, map_mul, h]

theorem map_velu2YR (x₀ y₀ x y : A) (hunit : IsUnit (x - x₀)) :
    f (velu2YR W x₀ y₀ x y) = velu2YR (W.map f) (f x₀) (f y₀) (f x) (f y) := by
  unfold velu2YR
  have h := map_ringInverse_of_isUnit f hunit
  rw [map_sub] at h
  simp only [map_veluGx, WeierstrassCurve.map_a₁, map_add, map_sub, map_mul, map_pow, h]

theorem map_veluQuotient2 (x₀ y₀ : A) :
    (W.veluQuotient2 x₀ y₀).map f = (W.map f).veluQuotient2 (f x₀) (f y₀) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp only [WeierstrassCurve.map_a₄, WeierstrassCurve.veluQuotient2_a₄, map_sub, map_mul, map_ofNat, map_veluGx]
  · simp only [WeierstrassCurve.map_a₆, WeierstrassCurve.veluQuotient2_a₆, WeierstrassCurve.map_b₂, map_sub, map_mul,
      map_ofNat, map_veluGx]

end Velu2R

end ModularCurve.TateVeluRing

end
