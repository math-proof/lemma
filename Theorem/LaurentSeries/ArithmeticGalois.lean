module

public import Theorem.HahnSeries.X0
public import Theorem.LaurentSeries.LaurentCoeff
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Abbrev.ModularCurve_ArithmeticGalois

public noncomputable section

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve Rat

namespace ModularCurve

section ArithmeticGalois

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))


@[simp]
public theorem coe_arithmeticRingAut_apply (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    (arithmeticRingAut F₀ σ x : LaurentSeries L) = coeffMap (σ : L →+* L) (x : LaurentSeries L) :=
  rfl


public theorem arithmeticRingAut_algebraMap (σ : L ≃ₐ[ℚ] L) (a : L) :
    arithmeticRingAut F₀ σ (algebraMap L (laurentBaseChange L F₀) a)
      = algebraMap L (laurentBaseChange L F₀) (σ a) :=
  Subtype.ext (coeffMap_algebraMap (σ : L →+* L) a)


@[simp]
public theorem toRingAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.toRingAut (arithmeticGalois F₀ σ) = arithmeticRingAut F₀ σ :=
  rfl


@[simp]
public theorem baseAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.baseAut (arithmeticGalois F₀ σ) = σ.toRingEquiv :=
  rfl


public theorem coe_arithmeticGalois_smul (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    ((arithmeticGalois F₀ σ • x : laurentBaseChange L F₀) : LaurentSeries L)
      = coeffMap (σ : L →+* L) (x : LaurentSeries L) :=
  rfl

end ArithmeticGalois

section ModularInstance

variable (N : ℕ)


@[simp]
public theorem JZero.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
    JZero.torsionGaloisRep N n σ x = arithmeticGalois (modularFunctionFieldFull N) σ • x :=
  rfl


public theorem JZero.coe_torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
    ((JZero.torsionGaloisRep N n σ x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
        JZero N) = arithmeticGalois (modularFunctionFieldFull N) σ • (x : JZero N) :=
  rfl

end ModularInstance

end ModularCurve
