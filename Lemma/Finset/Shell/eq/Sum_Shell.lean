import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
import Lemma.Finset.Kirillov.eq.Sum_Kirillov
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Finset


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)

@[path]
private lemma main
-- given
  (s : Finset ι)
  (f : ι → G → ℂ)
  (n : ℤ)
  (u : UF v) :
-- imply
  shell v ψ S ϖ (∑ i ∈ s, f i) n u = ∑ i ∈ s, shell v ψ S ϖ (f i) n u :=
-- proof
  Finset.Kirillov.eq.Sum_Kirillov v ψ S s f _

end LocalGL2.Kirillov

end


-- created on 2026-10-25
