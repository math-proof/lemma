import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.ChvMulUW.eq.MulChvUChvW
import Lemma.Nat.ChvM.eq.One
import Lemma.Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Int

noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ δ₁ : Γ}
-- given
  (hδ : δ ≤ δ₁)
  (χ : Ch v δ₁)
  (u : UF v) :
-- imply
  chv χ (rep v δ (u : Qm v δ)) = chv χ u := by
-- proof
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ) u
  have hm₁ : (m : UF v) ∈ Um v δ₁ :=
    (Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative v δ₁ m).mpr (((Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative v δ m).mp m.2).trans_le (Units.val_le_val.mpr hδ))
  show chv χ ((u : Qm v δ).out) = chv χ u
  rw [hm, Nat.ChvMulUW.eq.MulChvUChvW, Nat.ChvM.eq.One χ hm₁, mul_one]

end LocalGL2.Kirillov

end

-- created on 2026-10-25
