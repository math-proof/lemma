/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
import Def.StatisticalMechanics.Code.OSSS.TailCondLaw.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem atc_tailCondLawFixedDiag (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (t s m : ℕ) (hst : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, atc_fiberDiagFixed μ σ f e m s (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
  have hgC : ∀ ω, |f ω * Lindeberg.coord e ω| ≤ 1 := by
    intro ω; rw [abs_mul, ← one_mul (1 : ℝ)]
    exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num)
  have h := atc_innerFixed_eq_mean μ hpos hμ1 σ (g := fun ω => f ω * Lindeberg.coord e ω)
    hgC t s m hst A
  
  show atc_innerFixed μ σ (fun ω => f ω * Lindeberg.coord e ω) t A m s
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
  exact h


theorem atc_tailCondLawFixedMarg (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ} {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s m : ℕ) (hst : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, atc_fiberMargFixed μ σ g m s (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ g := by
  show atc_innerFixed μ σ g t A m s = Lindeberg.mean μ g
  exact atc_innerFixed_eq_mean μ hpos hμ1 σ hgC t s m hst A


lemma atc_hasFKG_ubfTail (n t : ℕ) : HasFKG (ubfTail n t) := by
  show HasFKG (Measure.pi (fun _ : {i : Fin n // ¬ (i : ℕ) < t} => unitMeasure))
  set ι := {i : Fin n // ¬ (i : ℕ) < t}
  set k := Fintype.card ι with hk
  set e : ι ≃ Fin k := Fintype.equivFin ι with he
  have hpi : HasFKG (Measure.pi (fun _ : Fin k => unitMeasure)) := hasFKG_pi_unitMeasure k
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e)
      (Measure.pi (fun _ : ι => unitMeasure)) (Measure.pi (fun _ : Fin k => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin k => unitMeasure) e
    convert h using 2
  refine hasFKG_of_orderIso _ _ (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e) hmp ?_ hpi
  intro p q hpq i
  have ep : ∀ (r : Fin k → ℝ),
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e).symm r) i = r (e i) := by
    intro r; simp [MeasurableEquiv.piCongrLeft]
  show ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e).symm p) i
      ≤ ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e).symm q) i
  rw [ep p, ep q]; exact hpq _


lemma atc_joint_meas_BV (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ)
    (t m s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A p.1) p.2 m s))) := by
  refine (measurable_g_codeMap μ σ g).comp ?_
  apply measurable_pi_lambda
  intro i; unfold adaptWt
  by_cases h1 : (i : ℕ) < s
  · simp only [h1, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h1, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]
      have hrw : (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) => acp_join t A p.1 i)
          = (fun p => if h : (i : ℕ) < t then A ⟨i, h⟩ else p.1 ⟨i, h⟩) := rfl
      rw [hrw]
      by_cases h3 : (i : ℕ) < t
      · simp only [dif_pos h3]; exact measurable_const
      · simp only [dif_neg h3]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h2, if_false]; exact (measurable_pi_apply i).comp measurable_snd


lemma atc_marg_meas_B (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ)
    (t m s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ =>
      ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)) :=
  (atc_joint_meas_BV μ σ g t m s A).stronglyMeasurable.integral_prod_right'.measurable


lemma atc_marg_mono_B {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ}
    (hg : Monotone g) {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg) (t m s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Monotone (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ =>
      ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)) := by
  intro B B' hBB
  apply integral_mono
  · exact ContinuousFKG.integrable_of_bdd _
      ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed m s).comp
        (measurable_const.prodMk measurable_id))) (fun V => hgC _)
  · exact ContinuousFKG.integrable_of_bdd _
      ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed m s).comp
        (measurable_const.prodMk measurable_id))) (fun V => hgC _)
  · intro V
    apply hg; apply codeMap_mono_u hpos hmono
    intro i; unfold adaptWt
    by_cases h1 : (i : ℕ) < s
    · simp [h1]
    · simp only [h1, if_false]
      by_cases h2 : (i : ℕ) < m
      · simp only [h2, if_true]
        have e1 : acp_join t A B i = if h : (i : ℕ) < t then A ⟨i, h⟩ else B ⟨i, h⟩ := rfl
        have e2 : acp_join t A B' i = if h : (i : ℕ) < t then A ⟨i, h⟩ else B' ⟨i, h⟩ := rfl
        rw [e1, e2]
        by_cases h3 : (i : ℕ) < t
        · rw [dif_pos h3, dif_pos h3]
        · rw [dif_neg h3, dif_neg h3]; exact hBB ⟨i, h3⟩
      · simp [h2]


lemma atc_marg_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ}
    (hgC : ∀ ω, |g ω| ≤ 1) (t m s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)| ≤ 1 := by
  calc |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)|
      ≤ ∫ V, |g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) := integral_mono
        (ContinuousFKG.integrable_of_bdd _
          ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed m s).comp
            (measurable_const.prodMk measurable_id))).abs
          (fun V => by rw [abs_abs]; exact hgC _))
        (integrable_const 1) (fun V => hgC _)
    _ = 1 := by simp


end AdaptDisintegration
end OSSS
end StatMech
