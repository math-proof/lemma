import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.Sum_SMul.eq.F
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ : Γ}
  {f : UF v → X}
-- given
  (hf : IsLvl v δ f)
  (h : ∀ χ : Ch v δ, comp v δ f χ = 0)
  (u : UF v) :
-- imply
  f u = 0 := by
-- proof
  rw [← Nat.Sum_SMul.eq.F v hf u]
  simp [h]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
