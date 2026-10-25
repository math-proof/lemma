-- Carved from Lemma/Definitions/Def_ModularCurve_ArithmeticGalois.lean: instance decls only.
import Lemma.ModularCurve.X0
import Lemma.ModularCurve.LaurentCoeff
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Lemma.ModularCurve.ArithmeticGalois

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve Rat

namespace ModularCurve


section PicAction

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

instance : SMul (L ≃ₐ[ℚ] L) (Pic0 L (laurentBaseChange L F₀)) where
  smul σ x := arithmeticGalois F₀ σ • x

instance : DistribMulAction (L ≃ₐ[ℚ] L) (Pic0 L (laurentBaseChange L F₀)) where
  one_smul x := by rw [galois_smul_pic0_def, map_one, one_smul]
  mul_smul σ τ x := by
    rw [galois_smul_pic0_def, galois_smul_pic0_def, galois_smul_pic0_def, map_mul, mul_smul]
  smul_zero σ := by rw [galois_smul_pic0_def, smul_zero]
  smul_add σ x y := by
    rw [galois_smul_pic0_def, galois_smul_pic0_def, galois_smul_pic0_def, smul_add]

end PicAction


end ModularCurve
end
