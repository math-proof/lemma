import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
import Lemma.Nat.FU.eq.FW
import Lemma.Nat.ChvU.eq.ChvW
import Lemma.Nat.EqChvS
import Lemma.Nat.Rep.eq.Q
import Lemma.Nat.Qmap.eq.U
import Lemma.Complex.qmap_surjective
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
  {δ' δ : Γ}
  {f : UF v → X}
-- given
  (h : δ' ≤ δ)
  (hf : IsLvl v δ f)
  (σ : Ch v δ) :
-- imply
  comp v δ' f (refineCh v h σ) = comp v δ f σ := by
-- proof
  classical
  unfold comp
  have hterm : ∀ q' : Qm v δ', chv (refineCh v h σ) (rep v δ' q') • f (rep v δ' q') =
      chv σ (rep v δ (qmap v h q')) • f (rep v δ (qmap v h q')) := by
    intro q'
    have hcl : ((rep v δ' q' : UF v) : Qm v δ) = ((rep v δ (qmap v h q') : UF v) : Qm v δ) := by
      rw [Nat.Rep.eq.Q, ← Nat.Qmap.eq.U v h, Nat.Rep.eq.Q]
    rw [Nat.EqChvS, Nat.ChvU.eq.ChvW v le_rfl σ hcl, Nat.FU.eq.FW v hf hcl]
  simp_rw [hterm]
  set nF : ℕ := (Finset.univ.filter fun q' : Qm v δ' => qmap v h q' = 1).card with hF
  have hfib : ∀ q : Qm v δ, (Finset.univ.filter fun q' : Qm v δ' => qmap v h q' = q).card = nF := by
    intro q
    exact MonoidHom.card_fiber_eq_of_mem_range (qmap v h) (Complex.qmap_surjective v h q) (Complex.qmap_surjective v h 1)
  have hsum : ∀ g : Qm v δ → X, ∑ q' : Qm v δ', g (qmap v h q') = ∑ q : Qm v δ, (nF : ℂ) • g q := by
    intro g
    rw [← Finset.sum_fiberwise' Finset.univ (qmap v h) g]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, hfib q, Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card (Qm v δ') : ℂ) = (Fintype.card (Qm v δ) : ℂ) * nF := by
    have h1 : Fintype.card (Qm v δ') = Fintype.card (Qm v δ) * nF := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise fun q' _ => Finset.mem_univ (qmap v h q')]
      simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [h1, Nat.cast_mul]
  have hF0 : (nF : ℂ) ≠ 0 := by
    have : 0 < nF := by
      rw [hF, Finset.card_pos]
      obtain ⟨q₁, hq₁⟩ := Complex.qmap_surjective v h 1
      exact ⟨q₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₁⟩⟩
    exact_mod_cast this.ne'
  rw [hsum fun q => chv σ (rep v δ q) • f (rep v δ q), ← Finset.smul_sum, smul_smul, hcard, mul_inv,
    mul_assoc, inv_mul_cancel₀ hF0, mul_one]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
