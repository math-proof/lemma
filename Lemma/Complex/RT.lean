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

@[path]
private lemma main
-- given
  (k₁ k₂ : G)
  (V : G → ℂ) :
-- imply
  rT v k₁ (rT v k₂ V) = rT v (k₁ * k₂) V := by
-- proof
  funext g; simp [mul_assoc]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
