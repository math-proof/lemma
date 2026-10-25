import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.AddAB.eq.MulAB
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {v} in
@[path]
private lemma main
  {δ : Γ}
-- given
  (χ : Ch v δ)
  (u w : UF v) :
-- imply
  chv χ (u * w) = chv χ u * chv χ w := by
-- proof
  unfold chv
  rw [QuotientGroup.mk_mul, ofMul_mul]
  exact Complex.AddAB.eq.MulAB (Ch.toChar χ) _ _

end LocalGL2.Kirillov

end


-- created on 2026-10-25
