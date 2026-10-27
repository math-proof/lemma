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
  {u w : UF v}
-- given
  (hf : IsLvl v δ f)
  (h : (u : Qm v δ) = (w : Qm v δ)) :
-- imply
  f u = f w := by
-- proof
  rw [QuotientGroup.eq] at h
  have hw : w = u * (u⁻¹ * w) := (mul_inv_cancel_left u w).symm
  rw [hw, hf u _ h]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
