import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.Kirillov.eq.MkQDefectSpan
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)

@[path]
private lemma main
-- given
  (V : G → ℂ) :
-- imply
  shell v ψ S ϖ V 0 (1 : UF v) = (defectSpan v ψ S).mkQ V := by
-- proof
  unfold shell
  rw [zpow_zero, OneMemClass.coe_one, mul_one, Complex.Kirillov.eq.MkQDefectSpan]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
