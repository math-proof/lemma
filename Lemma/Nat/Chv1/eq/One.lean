import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.Zero.eq.One
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
  (χ : Ch v δ) :
-- imply
  chv χ (1 : UF v) = 1 := by
-- proof
  unfold chv
  rw [QuotientGroup.mk_one, ofMul_one]
  exact Complex.Zero.eq.One (Ch.toChar χ)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
