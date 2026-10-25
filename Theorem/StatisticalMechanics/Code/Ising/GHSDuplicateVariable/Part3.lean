/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Def.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem isingExp2_factor (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a b => f a * g b)
      = isingExpectation G β h f * isingExpectation G β h g := by
  unfold isingExp2 isingExpectation
  simp only []
  have hb : ∀ a : ConfigSpace V,
      (∑ b : ConfigSpace V, isingProb G β h a * isingProb G β h b * (f a * g b))
        = (isingProb G β h a * f a) * (∑ b : ConfigSpace V, isingProb G β h b * g b) := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_); ring
  rw [Finset.sum_congr rfl (fun a _ => hb a), ← Finset.sum_mul]


theorem isingExp2_add (β h : ℝ) (F₁ F₂ : ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a b => F₁ a b + F₂ a b)
      = isingExp2 G β h F₁ + isingExp2 G β h F₂ := by
  unfold isingExp2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_); ring


theorem isingExp2_const_mul (β h : ℝ) (r : ℝ) (F : ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a b => r * F a b) = r * isingExp2 G β h F := by
  unfold isingExp2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_); ring


theorem isingExp2_factor_a (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExp2 G β h (fun a _ => f a) = isingExpectation G β h f := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp2_factor G β h f (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp2_factor_b (β h : ℝ) (g : ConfigSpace V → ℝ) :
    isingExp2 G β h (fun _ b => g b) = isingExpectation G β h g := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp2_factor G β h (fun _ => (1:ℝ)) g
  simpa [h1] using this


end Ising
end StatMech
