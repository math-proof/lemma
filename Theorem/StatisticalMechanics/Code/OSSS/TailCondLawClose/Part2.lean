/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailCondLaw.Part5
import Def.StatisticalMechanics.Code.OSSS.TailCondLawClose.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma atl_margRand_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (atl_margRand μ σ f g t s A) :=
  (atl_jointMeas μ σ f g t s A).stronglyMeasurable.integral_prod_right'.measurable


lemma atl_margRand_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f g : ConfigSpace E → ℝ) (hgC : ∀ ω, |g ω| ≤ 1) (t s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    |atl_margRand μ σ f g t s A B| ≤ 1 := by
  unfold atl_margRand
  calc |∫ V, g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n)|
      ≤ ∫ V, |g (codeMap μ (σ : Fin n → E)
          (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) := integral_mono
        (ContinuousFKG.integrable_of_bdd _
          ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed _ s).comp
            (measurable_const.prodMk measurable_id))).abs
          (fun V => by rw [abs_abs]; exact hgC _))
        (integrable_const 1) (fun V => hgC _)
    _ = 1 := by simp


theorem atl_marg_of_MP (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (g : ConfigSpace E → ℝ) {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hMP : atl_TailSelMP μ σ f t s A) :
    (∫ B, atl_margRand μ σ f g t s A B ∂(ubfTail n t)) = Lindeberg.mean μ g :=
  atl_innerRand_eq_mean μ hpos hμ1 σ g hgC t s A hMP


end AdaptDisintegration
end OSSS
end StatMech
