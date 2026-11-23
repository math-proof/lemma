module

public import Theorem.HahnSeries.X0
public import Theorem.LaurentSeries.LaurentCoeff
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Abbrev.ModularCurve_ArithmeticGalois

@[expose] public section

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

end ArithmeticGalois

section ModularInstance

variable (N : ℕ)

def JZero.torsionGaloisRep (n : ℕ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End (ZMod n) (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n) :=
  (SemilinearAut.torsionRep _ _ n).comp (arithmeticGalois (modularFunctionFieldFull N))

end ModularInstance

end ModularCurve

end

end
