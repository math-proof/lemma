module

public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

@[expose] public section

noncomputable section

namespace HahnSeries

variable {R : Type*} [CommRing R]

def hahnTwistFun (χ : Multiplicative ℚ →* Rˣ) (x : HahnSeries ℚ R) : HahnSeries ℚ R where
  coeff a := χ (Multiplicative.ofAdd a) * x.coeff a
  isPWO_support' := x.isPWO_support'.mono fun a ha => by
    simp only [Function.mem_support] at ha ⊢
    exact fun h => ha (by rw [h, mul_zero])

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

variable (R) in

def MonoChar : Subgroup (Multiplicative ℚ →* Rˣ) :=
  (MonoidHom.eval (Multiplicative.ofAdd (1 : ℚ))).ker

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

variable (R) in

def monodromy : Subgroup (HahnSeries ℚ R ≃ₐ[R] HahnSeries ℚ R) :=
  (MonoChar R).map hahnTwistHom

end HahnSeries

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private def fixedFun (σ : K ≃ₐ[k] K) (E : WeierstrassCurve K)
    (hE : E.map (σ : K →+* K) = E) : E.toAffine.Point → E.toAffine.Point := fun P =>
  match P with
  | 0 => 0
  | some x y h => some (σ x) (σ y) (nonsingular_of_fixed σ E hE h)

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

end WeierstrassCurve.Affine.Point

end

end
