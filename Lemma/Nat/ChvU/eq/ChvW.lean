import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.UmV.le.UmV
import Lemma.Nat.ChvMulUW.eq.MulChvUChvW
import Lemma.Nat.ChvM.eq.One
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ δ₁ : Γ}
  {u w : UF v}
-- given
  (hδ : δ ≤ δ₁)
  (h : (u : Qm v δ) = (w : Qm v δ))
  (τ : Ch v δ₁) :
-- imply
  chv τ u = chv τ w := by
-- proof
  rw [QuotientGroup.eq] at h
  have hw : w = u * (u⁻¹ * w) := (mul_inv_cancel_left u w).symm
  rw [hw, Nat.ChvMulUW.eq.MulChvUChvW, Nat.ChvM.eq.One τ (Nat.UmV.le.UmV v hδ h), mul_one]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
