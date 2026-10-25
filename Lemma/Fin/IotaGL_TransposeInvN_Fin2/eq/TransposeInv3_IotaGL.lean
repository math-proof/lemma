import Mathlib
import sympy.Basic
import Lemma.LanglandsTunnell.CubicInduction_Structure
open Matrix
open LanglandsTunnell.CubicInduction
set_option autoImplicit false


/--
[iotaGL_transposeInvN]
-/
@[path]
private lemma main
-- given
  {A : Type*} [CommRing A] (g : GL (Fin 2) A) :
-- imply
  iotaGL (transposeInvN (Fin 2) g) = transposeInv3 (iotaGL g) := by
-- proof
  refine Units.ext ?_
  change embedMat2 _ = (((iotaGL g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
  rw [← map_inv, coe_iotaGL, coe_transposeInvN]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]


-- created on 2026-10-24
