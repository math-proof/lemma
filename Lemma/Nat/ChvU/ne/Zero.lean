import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.ChvMulUW.eq.MulChvUChvW
import Lemma.Nat.Chv1.eq.One
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {v} in
@[path]
private lemma main
  {δ : Γ}
-- given
  (χ : Ch v δ)
  (u : UF v) :
-- imply
  chv χ u ≠ 0 := by
-- proof
  intro h
  have h1 := Nat.ChvMulUW.eq.MulChvUChvW χ u u⁻¹
  rw [mul_inv_cancel, Nat.Chv1.eq.One, h, zero_mul] at h1
  exact one_ne_zero h1

end LocalGL2.Kirillov

end


-- created on 2026-10-25
