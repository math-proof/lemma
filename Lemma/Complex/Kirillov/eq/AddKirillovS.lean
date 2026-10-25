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

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

@[path]
private lemma main
-- given
  (V W : G → ℂ)
  (a : Fx) :
-- imply
  kirillov v ψ S (V + W) a = kirillov v ψ S V a + kirillov v ψ S W a := by
-- proof
  unfold kirillov
  rw [map_add, map_add]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
