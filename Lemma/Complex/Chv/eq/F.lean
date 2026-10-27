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
  {f : UF v → ℂ}
-- given
  (hmul : ∀ u w : UF v, f (u * w) = f u * f w)
  (htriv : ∀ m ∈ Um v δ, f m = 1)
  (u : UF v) :
-- imply
  chv (chOfFun v δ f hmul htriv) u = f u := by
-- proof
  show f (rep v δ (Additive.toMul (Additive.ofMul (u : Qm v δ)))) = f u
  rw [toMul_ofMul]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ) u
  show f ((u : Qm v δ).out) = f u
  rw [hm, hmul, htriv m m.2, mul_one]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
