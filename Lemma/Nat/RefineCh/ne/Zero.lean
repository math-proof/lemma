import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.EqChvS
import Lemma.Nat.Chv_0U.eq.One
import Lemma.Nat.χ.eq.ρ
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
  {γ : Ch v δ₁}
-- given
  (h : δ ≤ δ₁)
  (hγ : γ ≠ 0) :
-- imply
  refineCh v h γ ≠ 0 := by
-- proof
  intro h0
  apply hγ
  apply Nat.χ.eq.ρ
  intro u
  rw [← Nat.EqChvS v h γ u, h0, Nat.Chv_0U.eq.One, Nat.Chv_0U.eq.One]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
