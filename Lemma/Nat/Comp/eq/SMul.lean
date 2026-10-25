import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.FU.eq.FW
import Lemma.Nat.ChvU.eq.ChvW
import Lemma.Nat.Chv_U.eq.ChvU
import Lemma.Nat.ChvMulUW.eq.MulChvUChvW
import Lemma.Nat.Rep.eq.Q
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
  (ν : UF v)
  (γ : Ch v δ) :
-- imply
  comp v δ (fun u => f (u * ν)) γ = (chv γ ν)⁻¹ • comp v δ f γ := by
-- proof
  unfold comp
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight ((ν : Qm v δ)⁻¹))]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.coe_mulRight]
  have h1 : ((rep v δ (q * (ν : Qm v δ)⁻¹) * ν : UF v) : Qm v δ) = ((rep v δ q : UF v) : Qm v δ) := by
    rw [QuotientGroup.mk_mul, Nat.Rep.eq.Q, Nat.Rep.eq.Q, inv_mul_cancel_right]
  have h2 : ((rep v δ (q * (ν : Qm v δ)⁻¹) : UF v) : Qm v δ) = ((rep v δ q * ν⁻¹ : UF v) : Qm v δ) := by
    rw [Nat.Rep.eq.Q, QuotientGroup.mk_mul, QuotientGroup.mk_inv, Nat.Rep.eq.Q]
  rw [Nat.FU.eq.FW v hf h1, Nat.ChvU.eq.ChvW v le_rfl γ h2, Nat.ChvMulUW.eq.MulChvUChvW, Nat.Chv_U.eq.ChvU, smul_smul, mul_comm]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
