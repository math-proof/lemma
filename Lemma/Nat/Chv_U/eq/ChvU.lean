import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.NegA.eq.A
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
  (u : UF v) :
-- imply
  chv χ u⁻¹ = (chv χ u)⁻¹ := by
-- proof
  unfold chv
  rw [QuotientGroup.mk_inv, ofMul_inv]
  exact Complex.NegA.eq.A (Ch.toChar χ) _

end LocalGL2.Kirillov

end


-- created on 2026-10-25
