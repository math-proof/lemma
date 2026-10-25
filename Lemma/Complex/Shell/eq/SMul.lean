import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.Kirillov.eq.SMul
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
  (c : ℂ)
  (V : G → ℂ)
  (n : ℤ)
  (u : UF v) :
-- imply
  shell v ψ S ϖ (c • V) n u = c • shell v ψ S ϖ V n u :=
-- proof
  Complex.Kirillov.eq.SMul v ψ S c V _

end LocalGL2.Kirillov

end


-- created on 2026-10-25
