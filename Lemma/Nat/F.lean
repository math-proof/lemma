import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField


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
  (u : UF v) :
-- imply
  f (rep v δ (u : Qm v δ)) = f u := by
-- proof
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ) u
  show f ((u : Qm v δ).out) = f u
  rw [hm]
  exact hf u m m.2

end LocalGL2.Kirillov

end


-- created on 2026-10-25
