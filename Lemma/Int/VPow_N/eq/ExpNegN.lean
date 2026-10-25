import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

include hϖ in
@[path]
private lemma main
-- given
  (n : ℤ) :
-- imply
  Valued.v (((ϖ ^ n : Fx) : F)) = WithZero.exp (-n) := by
-- proof
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
