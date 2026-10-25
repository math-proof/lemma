import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.DgOne
import Lemma.Complex.EqRTV
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

@[path]
private lemma main
-- given
  (V : G → ℂ) :
-- imply
  kirillov v ψ S V 1 = (defectSpan v ψ S).mkQ V := by
-- proof
  unfold kirillov
  rw [Nat.DgOne, Complex.EqRTV]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
