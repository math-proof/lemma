import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
import Lemma.Nat.F
import Lemma.Nat.Chv_U.eq.ChvU
import Lemma.Nat.ChvMulUW.eq.MulChvUChvW
import Lemma.Nat.MulRepU.eq.One.is.Q.eq.U
import Lemma.Complex.CardQmV.ne.Zero
import Lemma.Complex.Sum_ChvU.eq.U.eq.One
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Complex


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
  ∑ χ : Ch v δ, (chv χ u)⁻¹ • comp v δ f χ = f u := by
-- proof
  have h1 : ∀ χ : Ch v δ, (chv χ u)⁻¹ • comp v δ f χ =
      (Fintype.card (Qm v δ) : ℂ)⁻¹ • ∑ q : Qm v δ, chv χ (rep v δ q * u⁻¹) • f (rep v δ q) := by
    intro χ
    unfold comp
    rw [smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul, Nat.ChvMulUW.eq.MulChvUChvW, Nat.Chv_U.eq.ChvU, mul_comm]
  have h2 : ∀ q : Qm v δ, (∑ χ : Ch v δ, chv χ (rep v δ q * u⁻¹)) • f (rep v δ q) =
      if q = (u : Qm v δ) then (Fintype.card (Qm v δ) : ℂ) • f (rep v δ q) else 0 := by
    intro q
    rw [Complex.Sum_ChvU.eq.U.eq.One, ite_smul, zero_smul]
    exact if_congr (Nat.MulRepU.eq.One.is.Q.eq.U v δ q u) rfl rfl
  calc
    _ = (Fintype.card (Qm v δ) : ℂ)⁻¹ •
        ∑ χ : Ch v δ, ∑ q : Qm v δ, chv χ (rep v δ q * u⁻¹) • f (rep v δ q) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun χ _ => h1 χ
    _ = (Fintype.card (Qm v δ) : ℂ)⁻¹ •
        ∑ q : Qm v δ, (∑ χ : Ch v δ, chv χ (rep v δ q * u⁻¹)) • f (rep v δ q) := by
      rw [Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun q _ => (Finset.sum_smul).symm
    _ = (Fintype.card (Qm v δ) : ℂ)⁻¹ • ((Fintype.card (Qm v δ) : ℂ) • f (rep v δ (u : Qm v δ))) := by
      congr 1
      simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = f u := by
      rw [smul_smul, inv_mul_cancel₀ (Complex.CardQmV.ne.Zero v δ), one_smul, Nat.F v hf]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
