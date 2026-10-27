import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.Comp.eq.SMul
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
-- given
  (δ : Γ)
  (c : ℂ)
  (g : UF v → ℂ)
  (γ : Ch v δ) :
-- imply
  comp v δ (fun u => c * g u) γ = c * comp v δ g γ :=
-- proof
  Complex.Comp.eq.SMul v δ c g γ

end LocalGL2.Kirillov

end


-- created on 2026-10-25
