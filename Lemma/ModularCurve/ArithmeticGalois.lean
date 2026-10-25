import Lemma.ModularCurve.X0
import Lemma.ModularCurve.LaurentCoeff
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Instance.ModularCurve_ArithmeticGalois
import Abbrev.ModularCurve_ArithmeticGalois

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve Rat

namespace ModularCurve

section ArithmeticGalois

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def arithmeticRingAut (σ : L ≃ₐ[ℚ] L) :
    (laurentBaseChange L F₀) ≃+* (laurentBaseChange L F₀) where
  toFun x := ⟨coeffMap (σ : L →+* L) (x : LaurentSeries L),
    coeffMap_mem_laurentBaseChange σ x.2⟩
  invFun x := ⟨coeffMap (σ.symm : L →+* L) (x : LaurentSeries L),
    coeffMap_mem_laurentBaseChange σ.symm x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (σ.symm : L →+* L) (coeffMap (σ : L →+* L) (x : LaurentSeries L))
      = (x : LaurentSeries L)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id L) (RingHom.ext fun a => σ.symm_apply_apply a)
        (x : LaurentSeries L),
      coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (σ : L →+* L) (coeffMap (σ.symm : L →+* L) (x : LaurentSeries L))
      = (x : LaurentSeries L)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id L) (RingHom.ext fun a => σ.apply_symm_apply a)
        (x : LaurentSeries L),
      coeffMap_id]
  map_mul' x y :=
    Subtype.ext (map_mul (coeffMap (σ : L →+* L)) (x : LaurentSeries L) (y : LaurentSeries L))
  map_add' x y :=
    Subtype.ext (map_add (coeffMap (σ : L →+* L)) (x : LaurentSeries L) (y : LaurentSeries L))

@[simp]
theorem coe_arithmeticRingAut_apply (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    (arithmeticRingAut F₀ σ x : LaurentSeries L) = coeffMap (σ : L →+* L) (x : LaurentSeries L) :=
  rfl

theorem arithmeticRingAut_algebraMap (σ : L ≃ₐ[ℚ] L) (a : L) :
    arithmeticRingAut F₀ σ (algebraMap L (laurentBaseChange L F₀) a)
      = algebraMap L (laurentBaseChange L F₀) (σ a) :=
  Subtype.ext (coeffMap_algebraMap (σ : L →+* L) a)

def arithmeticGalois : (L ≃ₐ[ℚ] L) →* SemilinearAut L (laurentBaseChange L F₀) where
  toFun σ := ⟨(arithmeticRingAut F₀ σ, σ.toRingEquiv), fun a => arithmeticRingAut_algebraMap F₀ σ a⟩
  map_one' := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext ?_) rfl)
    show coeffMap ((1 : L ≃ₐ[ℚ] L) : L →+* L) (x : LaurentSeries L) = (x : LaurentSeries L)
    rw [show ((1 : L ≃ₐ[ℚ] L) : L →+* L) = RingHom.id L from RingHom.ext fun _ => rfl,
      coeffMap_id]
  map_mul' σ τ := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext ?_) rfl)
    show coeffMap ((σ * τ : L ≃ₐ[ℚ] L) : L →+* L) (x : LaurentSeries L)
      = coeffMap (σ : L →+* L) (coeffMap (τ : L →+* L) (x : LaurentSeries L))
    rw [coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun _ => rfl) _

@[simp]
theorem toRingAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.toRingAut (arithmeticGalois F₀ σ) = arithmeticRingAut F₀ σ :=
  rfl

@[simp]
theorem baseAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.baseAut (arithmeticGalois F₀ σ) = σ.toRingEquiv :=
  rfl

theorem coe_arithmeticGalois_smul (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    ((arithmeticGalois F₀ σ • x : laurentBaseChange L F₀) : LaurentSeries L)
      = coeffMap (σ : L →+* L) (x : LaurentSeries L) :=
  rfl

end ArithmeticGalois

section PicAction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem galois_smul_pic0_def (σ : L ≃ₐ[ℚ] L) (x : Pic0 L (laurentBaseChange L F₀)) :
    σ • x = arithmeticGalois F₀ σ • x :=
  rfl

end PicAction

section ModularInstance

variable (N : ℕ)

example : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero N) :=
  inferInstance

def JZero.torsionGaloisRep (n : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (ZMod n) (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :=
  (SemilinearAut.torsionRep _ _ n).comp (arithmeticGalois (modularFunctionFieldFull N))

@[simp]
theorem JZero.torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
    JZero.torsionGaloisRep N n σ x = arithmeticGalois (modularFunctionFieldFull N) σ • x :=
  rfl

theorem JZero.coe_torsionGaloisRep_apply {n : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
    ((JZero.torsionGaloisRep N n σ x : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :
        JZero N) = σ • (x : JZero N) :=
  rfl

end ModularInstance

end ModularCurve
