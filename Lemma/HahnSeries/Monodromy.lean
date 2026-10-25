import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

namespace HahnSeries

variable {R : Type*} [CommRing R]

def hahnTwistFun (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) : HahnSeries ℚ R where
  coeff a := χ (Multiplicative.ofAdd a) * x.coeff a
  isPWO_support' := x.isPWO_support'.mono fun a ha => by
    simp only [Function.mem_support] at ha ⊢
    exact fun h => ha (by rw [h, mul_zero])

theorem coeff_hahnTwistFun (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) (a : ℚ) :
    (hahnTwistFun χ x).coeff a = χ (Multiplicative.ofAdd a) * x.coeff a :=
  rfl

theorem support_hahnTwistFun (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) :
    (hahnTwistFun χ x).support = x.support := by
  ext a
  rw [mem_support, mem_support, coeff_hahnTwistFun]
  exact not_congr (Units.mul_right_eq_zero _)

theorem hahnTwistFun_single (χ : Multiplicative ℚ →* Rˣ) (a : ℚ) (r : R) :
    hahnTwistFun χ (single a r) = single a (χ (Multiplicative.ofAdd a) * r) := by
  ext b
  rw [coeff_hahnTwistFun]
  by_cases hb : b = a
  · subst hb
    rw [coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne hb, coeff_single_of_ne hb, mul_zero]

def hahnTwist (χ : Multiplicative ℚ →* Rˣ) : HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R where
  toFun := hahnTwistFun χ
  invFun := hahnTwistFun χ⁻¹
  left_inv x := by
    ext a
    rw [coeff_hahnTwistFun, coeff_hahnTwistFun, ← mul_assoc, ← Units.val_mul,
      MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, one_mul]
  right_inv x := by
    ext a
    rw [coeff_hahnTwistFun, coeff_hahnTwistFun, ← mul_assoc, ← Units.val_mul,
      MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_mul]
  map_mul' x y := by
    ext a
    have hset : Finset.antidiagonal (hahnTwistFun χ x).isPWO_support
        (hahnTwistFun χ y).isPWO_support a =
        Finset.antidiagonal x.isPWO_support y.isPWO_support a := by
      ext ij
      simp only [Finset.mem_antidiagonal, support_hahnTwistFun]
    rw [coeff_hahnTwistFun, coeff_mul, coeff_mul, hset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hij
    rw [coeff_hahnTwistFun, coeff_hahnTwistFun, mul_mul_mul_comm, ← Units.val_mul, ← map_mul,
      ← ofAdd_add, hsum]
  map_add' x y := by
    ext a
    rw [coeff_hahnTwistFun, coeff_add, coeff_add, coeff_hahnTwistFun, coeff_hahnTwistFun,
      mul_add]
  commutes' r := by
    have hC : algebraMap R (HahnSeries ℚ R) r = HahnSeries.C r := by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
    have hCs : (HahnSeries.C r : HahnSeries ℚ R) = single (0 : ℚ) r := rfl
    show hahnTwistFun χ _ = _
    rw [hC, hCs, hahnTwistFun_single, ofAdd_zero, map_one, Units.val_one, one_mul]

@[simp]
theorem coeff_hahnTwist (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) (a : ℚ) :
    (hahnTwist χ x).coeff a = χ (Multiplicative.ofAdd a) * x.coeff a :=
  rfl

theorem hahnTwist_single (χ : Multiplicative ℚ →* Rˣ) (a : ℚ) (r : R) :
    hahnTwist χ (single a r) = single a (χ (Multiplicative.ofAdd a) * r) :=
  hahnTwistFun_single χ a r

theorem support_hahnTwist (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) :
    (hahnTwist χ x).support = x.support :=
  support_hahnTwistFun χ x

theorem order_hahnTwist (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) :
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

def MonoChar : Subgroup (Multiplicative ℚ →* Rˣ) :=
  (MonoidHom.eval (Multiplicative.ofAdd (1 : ℚ))).ker

theorem mem_monoChar_iff {χ : Multiplicative ℚ →* Rˣ} :
    χ ∈ MonoChar R ↔ χ (Multiplicative.ofAdd (1 : ℚ)) = 1 :=
  Iff.rfl

def hahnTwistHom : (Multiplicative ℚ →* Rˣ) →* (HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R) where
  toFun := hahnTwist
  map_one' := by
    refine AlgEquiv.ext fun x => ?_
    ext a
    rw [coeff_hahnTwist, MonoidHom.one_apply, Units.val_one, one_mul, AlgEquiv.one_apply]
  map_mul' χ₁ χ₂ := by
    refine AlgEquiv.ext fun x => ?_
    ext a
    rw [coeff_hahnTwist, AlgEquiv.mul_apply, coeff_hahnTwist, coeff_hahnTwist,
      MonoidHom.mul_apply, Units.val_mul, mul_assoc]

theorem hahnTwistHom_apply (χ : Multiplicative ℚ →* Rˣ) :
    (hahnTwistHom : (Multiplicative ℚ →* Rˣ) →* (HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R)) χ =
      hahnTwist χ :=
  rfl

variable (R) in

def monodromy : Subgroup (HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R) :=
  (MonoChar R).map hahnTwistHom

theorem fixes_single_one_of_mem_monodromy {m : HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R}
    (hm : m ∈ monodromy R) :
    m (single (1 : ℚ) (1 : R)) = single (1 : ℚ) (1 : R) := by
  obtain ⟨χ, hχ, rfl⟩ := hm
  rw [hahnTwistHom_apply, hahnTwist_single, mem_monoChar_iff.mp hχ, Units.val_one, one_mul]

end HahnSeries

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem nonsingular_of_fixed (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) {x y : K} (h : E.toAffine.Nonsingular x y) :
    E.toAffine.Nonsingular (σ x) (σ y) := by
  have hE2 : E.toAffine.map (σ : K →+* K) = E.toAffine := hE
  have h' := (Affine.map_nonsingular (W := E.toAffine) (f := (σ : K →+* K))
    σ.injective x y).mpr h
  rwa [hE2] at h'

private def fixedFun (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : E.toAffine.Point → E.toAffine.Point := fun P =>
  match P with
  | 0 => 0
  | some x y h => some (σ x) (σ y) (nonsingular_of_fixed σ E hE h)

private theorem map_symm_eq (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : E.map (σ.symm : K →+* K) = E := by
  conv_lhs => rw [← hE]
  rw [WeierstrassCurve.map_map]
  have h : (σ.symm : K →+* K).comp (σ : K →+* K) = RingHom.id K := by
    ext z
    exact σ.symm_apply_apply z
  rw [h, WeierstrassCurve.map_id]

private theorem fixedFun_add [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
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

def fixedTransport [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : E.toAffine.Point ≃+ E.toAffine.Point where
  toFun := fixedFun σ E hE
  invFun := fixedFun σ.symm E (map_symm_eq σ E hE)
  left_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · show some _ _ _ = some x y h
      congr 1
      · exact σ.symm_apply_apply x
      · exact σ.symm_apply_apply y
  right_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · show some _ _ _ = some x y h
      congr 1
      · exact σ.apply_symm_apply x
      · exact σ.apply_symm_apply y
  map_add' := fixedFun_add σ E hE

theorem fixedTransport_zero [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : fixedTransport σ E hE 0 = 0 :=
  rfl

theorem fixedTransport_some [DecidableEq K] (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) (x y : K) (h : E.toAffine.Nonsingular x y) :
    fixedTransport σ E hE (some x y h) = some (σ x) (σ y) (nonsingular_of_fixed σ E hE h) :=
  rfl

end WeierstrassCurve.Affine.Point

end
