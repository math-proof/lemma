/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.OrderClosed
import Def.StatisticalMechanics.Code.OSSS.Integration
open scoped BigOperators
open Real Set Finset Filter Topology

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Integration

theorem hasDerivAt_meanLogTerm (fseq fpseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hf : ∀ i, HasDerivAt (fun x => fseq i x) (fpseq i x) x) :
    HasDerivAt (fun x => meanLogTerm fseq n x)
      ((1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ)) x := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  exact (hf i).div_const (i : ℝ)


theorem deriv_meanLogTerm_lower (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (n : ℕ) (x : ℝ) (hlogn : 0 < Real.log n)
    (hSrec : ∀ i, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i x)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x) :
    (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n
      ≤ (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ) := by
  have hnum := logStep_sum_le_sum_deriv (fun i => fseq i x) (fun i => fpseq i x)
    (fun i => Sig i x) n hSrec hfnn hSpos hdiff
  rw [div_eq_inv_mul, one_div]
  exact mul_le_mul_of_nonneg_left hnum (by positivity)


theorem integrated_meanField (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (n : ℕ) (β' β m : ℝ) (hββ : β' ≤ β) (hlogn : 0 < Real.log n)
    (hf : ∀ i x, x ∈ Icc β' β → HasDerivAt (fun x => fseq i x) (fpseq i x) x)
    (hSrec : ∀ i x, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i x, 1 ≤ i → x ∈ Icc β' β → 0 ≤ fseq i x)
    (hSpos : ∀ i x, 1 ≤ i → x ∈ Icc β' β → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, ∀ x, 1 ≤ i → x ∈ Icc β' β → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x)
    (hm : ∀ x ∈ Icc β' β, m ≤ (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n) :
    (β - β') * m ≤ meanLogTerm fseq n β - meanLogTerm fseq n β' := by
  rw [mul_comm]
  
  apply slope_ge_of_deriv_ge β' β m hββ
    (fun x => meanLogTerm fseq n x)
    (fun x => (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ))
  · intro x hx
    exact hasDerivAt_meanLogTerm fseq fpseq n x (fun i => hf i x hx)
  · intro x hx
    refine le_trans (hm x hx) ?_
    exact deriv_meanLogTerm_lower fseq fpseq Sig n x hlogn
      (fun i => hSrec i x) (fun i hi => hfnn i x hi hx)
      (fun i hi => hSpos i x hi hx) (fun i hi => hdiff i x hi hx)


theorem meanField_limit (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hm : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    (β - β') * m ≤ fβ - fβ' := by
  
  have hlhs : Tendsto (fun n => (β - β') * mseq n) atTop (𝓝 ((β - β') * m)) :=
    hm.const_mul (β - β')
  have hrhs : Tendsto (fun n => T n β - T n β') atTop (𝓝 (fβ - fβ')) := hTβ.sub hTβ'
  exact le_of_tendsto_of_tendsto hlhs hrhs hbound


theorem meanField_lower (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    β - β' ≤ fβ - fβ' := by
  have hmain := meanField_limit T mseq β' β fβ fβ' m hTβ hTβ' hmlim hbound
  have hβsub : 0 ≤ β - β' := by linarith
  calc β - β' = (β - β') * 1 := by ring
    _ ≤ (β - β') * m := mul_le_mul_of_nonneg_left hm1 hβsub
    _ ≤ fβ - fβ' := hmain

end OSSS.Integration
end StatMech
