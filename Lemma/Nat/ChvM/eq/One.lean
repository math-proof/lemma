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
  {m : UF v}
-- given
  (hm : m ∈ Um v δ)
  (χ : Ch v δ) :
-- imply
  chv χ m = 1 := by
-- proof
  unfold chv
  rw [(QuotientGroup.eq_one_iff m).mpr hm, ofMul_one]
  exact Complex.Zero.eq.One (Ch.toChar χ)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
