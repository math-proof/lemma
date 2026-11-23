module

public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

public noncomputable section

noncomputable section

namespace HahnSeries

variable {R : Type*} [CommRing R]


public theorem coeff_hahnTwistFun (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) (a : ℚ) :
    (hahnTwistFun χ x).coeff a = χ (Multiplicative.ofAdd a) * x.coeff a :=
  rfl


public theorem support_hahnTwistFun (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) :
    (hahnTwistFun χ x).support = x.support := by
  ext a
  rw [mem_support, mem_support, coeff_hahnTwistFun]
  exact not_congr (Units.mul_right_eq_zero _)


public theorem hahnTwistFun_single (χ : Multiplicative ℚ →* Rˣ) (a : ℚ) (r : R) :
    hahnTwistFun χ (single a r) = single a (χ (Multiplicative.ofAdd a) * r) := by
  ext b
  rw [coeff_hahnTwistFun]
  by_cases hb : b = a
  · subst hb
    rw [coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne hb, coeff_single_of_ne hb, mul_zero]


@[simp]
public theorem coeff_hahnTwist (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) (a : ℚ) :
    (hahnTwist χ x).coeff a = χ (Multiplicative.ofAdd a) * x.coeff a :=
  rfl


public theorem hahnTwist_single (χ : Multiplicative ℚ →* Rˣ) (a : ℚ) (r : R) :
    hahnTwist χ (single a r) = single a (χ (Multiplicative.ofAdd a) * r) :=
  hahnTwistFun_single χ a r


public theorem support_hahnTwist (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) :
    (hahnTwist χ x).support = x.support :=
  support_hahnTwistFun χ x


public theorem order_hahnTwist (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) :
    (hahnTwist χ x).order = x.order := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  · have hx' : hahnTwist χ x ≠ 0 := fun h =>
      hx ((hahnTwist χ).injective (by rw [h, map_zero]))
    refine le_antisymm (order_le_of_coeff_ne_zero ?_) (order_le_of_coeff_ne_zero ?_)
    · rw [coeff_hahnTwist]
      exact fun h0 => hx (coeff_order_eq_zero.mp ((Units.mul_right_eq_zero _).mp h0))
    · exact fun h0 => hx' (coeff_order_eq_zero.mp (by rw [coeff_hahnTwist, h0, mul_zero]))

variable (R) in


public theorem mem_monoChar_iff {χ : Multiplicative ℚ →* Rˣ} :
    χ ∈ MonoChar R ↔ χ (Multiplicative.ofAdd (1 : ℚ)) = 1 :=
  Iff.rfl


public theorem hahnTwistHom_apply (χ : Multiplicative ℚ →* Rˣ) :
    (hahnTwistHom : (Multiplicative ℚ →* Rˣ) →* (HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R)) χ =
      hahnTwist χ :=
  rfl

variable (R) in


public theorem fixes_single_one_of_mem_monodromy {m : HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R}
    (hm : m ∈ monodromy R) :
    m (single (1 : ℚ) (1 : R)) = single (1 : ℚ) (1 : R) := by
  obtain ⟨χ, hχ, rfl⟩ := hm
  rw [hahnTwistHom_apply, hahnTwist_single, mem_monoChar_iff.mp hχ, Units.val_one, one_mul]

end HahnSeries

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]


public theorem nonsingular_of_fixed (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) {x y : K} (h : E.toAffine.Nonsingular x y) :
    E.toAffine.Nonsingular (σ x) (σ y) := by
  have hE2 : E.toAffine.map (σ : K →+* K) = E.toAffine := hE
  have h' := (Affine.map_nonsingular (W := E.toAffine) (f := (σ : K →+* K))
    σ.injective x y).mpr h
  rwa [hE2] at h'


public theorem map_symm_eq (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : E.map (σ.symm : K →+* K) = E := by
  conv_lhs => rw [← hE]
  rw [WeierstrassCurve.map_map]
  have h : (σ.symm : K →+* K).comp (σ : K →+* K) = RingHom.id K := by
    ext z
    exact σ.symm_apply_apply z
  rw [h, WeierstrassCurve.map_id]


public theorem fixedFun_add [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) (P Q : E.toAffine.Point) :
    fixedFun σ E hE (P + Q) = fixedFun σ E hE P + fixedFun σ E hE Q := by
  have hE2 : E.toAffine.map (σ : K →+* K) = E.toAffine := hE
  have hneg : ∀ x y : K, E.toAffine.negY (σ x) (σ y) = σ (E.toAffine.negY x y) := by
    intro x y
    conv_lhs => rw [← hE2]
    exact Affine.map_negY (W' := E.toAffine) (σ : K →+* K) x y
  have hslope : ∀ x₁ x₂ y₁ y₂ : K,
      E.toAffine.slope (σ x₁) (σ x₂) (σ y₁) (σ y₂) = σ (E.toAffine.slope x₁ x₂ y₁ y₂) := by
    intro x₁ x₂ y₁ y₂
    conv_lhs => rw [← hE2]
    exact Affine.map_slope (W := E.toAffine) (σ : K →+* K) x₁ x₂ y₁ y₂
  have haddX : ∀ x₁ x₂ ℓ : K,
      E.toAffine.addX (σ x₁) (σ x₂) (σ ℓ) = σ (E.toAffine.addX x₁ x₂ ℓ) := by
    intro x₁ x₂ ℓ
    conv_lhs => rw [← hE2]
    exact Affine.map_addX (W' := E.toAffine) (σ : K →+* K) x₁ x₂ ℓ
  have haddY : ∀ x₁ x₂ y₁ ℓ : K,
      E.toAffine.addY (σ x₁) (σ x₂) (σ y₁) (σ ℓ) = σ (E.toAffine.addY x₁ x₂ y₁ ℓ) := by
    intro x₁ x₂ y₁ ℓ
    conv_lhs => rw [← hE2]
    exact Affine.map_addY (W' := E.toAffine) (f := (σ : K →+* K)) (x₁ := x₁) (x₂ := x₂)
      (y₁ := y₁) (ℓ := ℓ)
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂
  · rw [add_of_Y_eq hxy.1 hxy.2]
    exact (add_of_Y_eq (congrArg σ hxy.1) (by rw [hxy.2, hneg])).symm
  · have hxy' : ¬(σ x₁ = σ x₂ ∧ σ y₁ = E.toAffine.negY (σ x₂) (σ y₂)) := fun h =>
      hxy ⟨σ.injective h.1, σ.injective (by rw [hneg] at h; exact h.2)⟩
    rw [add_some hxy]
    show some _ _ _ = some _ _ _ + some _ _ _
    rw [add_some hxy']
    congr 1
    · rw [hslope, haddX]
    · rw [hslope, haddY]


public theorem fixedTransport_zero [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : fixedTransport σ E hE 0 = 0 :=
  rfl


public theorem fixedTransport_some [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) (x y : K) (h : E.toAffine.Nonsingular x y) :
    fixedTransport σ E hE (some x y h) = some (σ x) (σ y) (nonsingular_of_fixed σ E hE h) :=
  rfl

end WeierstrassCurve.Affine.Point

end
