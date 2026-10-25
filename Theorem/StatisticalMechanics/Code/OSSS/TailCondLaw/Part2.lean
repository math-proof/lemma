/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
import Def.StatisticalMechanics.Code.OSSS.TailCondLaw
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


lemma atc_innerFixed_const_head (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (t s m : ℕ) (hst : t ≤ s)
    (A A' : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atc_innerFixed μ σ g t A m s = atc_innerFixed μ σ g t A' m s := by
  unfold atc_innerFixed
  congr 1; funext B; congr 1; funext V
  rw [atc_adaptWt_join_indep_head t s m hst A A' B V]


lemma atc_avg_innerFixed (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ} {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg)
    (t m s : ℕ) :
    (∫ A, atc_innerFixed μ σ g t A m s ∂(ubfHead n t)) = ∑ x, g x * μ x := by
  
  have hfull := adsD_integral_g_adaptWt_fixed μ hpos hμ1 σ g s m
  have hgmeas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) :=
    (measurable_g_codeMap μ σ g).comp (measurable_adaptWt_fixed m s)
  have hgbdd : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      |g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))| ≤ Cg := fun p => hgC _
  
  set φ : (Fin n → ℝ) → ℝ := fun U =>
    ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt U V m s)) ∂(Vcube n) with hφ
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) ((Vcube n).prod (Vcube n)) :=
    ContinuousFKG.integrable_of_bdd _ hgmeas hgbdd
  have hfubini : (∫ p, g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))
        ∂((Vcube n).prod (Vcube n)))
      = ∫ U, φ U ∂(Vcube n) := by rw [integral_prod _ hint]
  have hφm : Measurable φ := by
    rw [hφ]; exact hgmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hφC : ∀ U, |φ U| ≤ Cg := by
    intro U; rw [hφ]
    calc |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt U V m s)) ∂(Vcube n)|
        ≤ ∫ V, |g (codeMap μ (σ : Fin n → E) (adaptWt U V m s))| ∂(Vcube n) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ V, Cg ∂(Vcube n) := integral_mono
          (ContinuousFKG.integrable_of_bdd _
            ((measurable_g_codeMap μ σ g).comp
              ((measurable_adaptWt_fixed m s).comp (measurable_const.prodMk measurable_id))).abs
            (fun V => by rw [abs_abs]; exact hgC _))
          (integrable_const Cg) (fun V => hgC _)
      _ = Cg := by simp
  
  have hsplit : (∫ U, φ U ∂(cube n))
      = ∫ A, (∫ B, φ ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := by
    have h := ubf_integral_factor n t
      (h₀ := fun _ : {i : Fin n // (i : ℕ) < t} → ℝ => (1 : ℝ))
      measurable_const (Ch := 1) (fun _ => by norm_num) hφm hφC
    simpa using h
  rw [hfull] at hfubini
  
  have key : (∫ A, atc_innerFixed μ σ g t A m s ∂(ubfHead n t))
      = ∫ A, (∫ B, φ ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := rfl
  rw [key, ← hsplit]
  exact hfubini.symm


theorem atc_innerFixed_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ} {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s m : ℕ) (hst : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atc_innerFixed μ σ g t A m s = Lindeberg.mean μ g := by
  
  
  have hconst : ∀ A', atc_innerFixed μ σ g t A' m s = atc_innerFixed μ σ g t A m s :=
    fun A' => atc_innerFixed_const_head μ σ g t s m hst A' A
  have havg : (∫ A', atc_innerFixed μ σ g t A' m s ∂(ubfHead n t)) = ∑ x, g x * μ x :=
    atc_avg_innerFixed μ hpos hμ1 σ hgC t m s
  show atc_innerFixed μ σ g t A m s = ∑ x, g x * μ x
  rw [← havg]
  rw [show (∫ A', atc_innerFixed μ σ g t A' m s ∂(ubfHead n t))
        = ∫ _A', atc_innerFixed μ σ g t A m s ∂(ubfHead n t) from by
    congr 1; funext A'; exact hconst A']
  rw [integral_const, probReal_univ]; simp


end AdaptDisintegration
end OSSS
end StatMech
