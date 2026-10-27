import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
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
  (s : Finset ι)
  (f : ι → G → ℂ)
  (a : Fx) :
-- imply
  kirillov v ψ S (∑ i ∈ s, f i) a = ∑ i ∈ s, kirillov v ψ S (f i) a := by
-- proof
  have h : kirillov v ψ S (∑ i ∈ s, f i) a = ((defectSpan v ψ S).mkQ.comp (rT v (dg v a))) (∑ i ∈ s, f i) := rfl
  rw [h, map_sum]
  rfl

end LocalGL2.Kirillov

end


-- created on 2026-10-25
