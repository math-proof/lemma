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
import Def.StatisticalMechanics.Code.Ising.GHSDuplicateVariable
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem isingExp3_factor (β h : ℝ) (f g k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => f a * g b * k c)
      = isingExpectation G β h f * isingExpectation G β h g * isingExpectation G β h k := by
  unfold isingExp3 isingExpectation
  simp only []
  
  have hc : ∀ a b : ConfigSpace V,
      (∑ c : ConfigSpace V,
          isingProb G β h a * isingProb G β h b * isingProb G β h c * (f a * g b * k c))
        = (isingProb G β h a * f a) * (isingProb G β h b * g b)
            * (∑ c : ConfigSpace V, isingProb G β h c * k c) := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_); ring
  have hb : ∀ a : ConfigSpace V,
      (∑ b : ConfigSpace V, ∑ c : ConfigSpace V,
          isingProb G β h a * isingProb G β h b * isingProb G β h c * (f a * g b * k c))
        = (isingProb G β h a * f a)
            * (∑ b : ConfigSpace V, isingProb G β h b * g b)
            * (∑ c : ConfigSpace V, isingProb G β h c * k c) := by
    intro a
    rw [Finset.sum_congr rfl (fun b _ => hc a b), ← Finset.sum_mul, ← Finset.mul_sum,
      mul_assoc]
  rw [Finset.sum_congr rfl (fun a _ => hb a), ← Finset.sum_mul, ← Finset.sum_mul]


@[simp] theorem isingExp3_one (β h : ℝ) :
    isingExp3 G β h (fun _ _ _ => (1 : ℝ)) = 1 := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_c (β h : ℝ) (k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun _ _ c => k c) = isingExpectation G β h k := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) k
  simpa [h1] using this


theorem isingExp3_factor_b (β h : ℝ) (g : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun _ b _ => g b) = isingExpectation G β h g := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) g (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_a (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a _ _ => f a) = isingExpectation G β h f := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h f (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_ab (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b _ => f a * g b)
      = isingExpectation G β h f * isingExpectation G β h g := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h f g (fun _ => (1:ℝ))
  simpa [h1] using this


theorem isingExp3_factor_ac (β h : ℝ) (f k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a _ c => f a * k c)
      = isingExpectation G β h f * isingExpectation G β h k := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h f (fun _ => (1:ℝ)) k
  simpa [h1] using this


theorem isingExp3_factor_bc (β h : ℝ) (g k : ConfigSpace V → ℝ) :
    isingExp3 G β h (fun _ b c => g b * k c)
      = isingExpectation G β h g * isingExpectation G β h k := by
  have h1 : isingExpectation G β h (fun _ : ConfigSpace V => (1 : ℝ)) = 1 := by
    unfold isingExpectation; simp [isingProb_sum_eq_one G β h]
  have := isingExp3_factor G β h (fun _ => (1:ℝ)) g k
  simpa [h1] using this


theorem isingExp3_add (β h : ℝ)
    (F₁ F₂ : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => F₁ a b c + F₂ a b c)
      = isingExp3 G β h F₁ + isingExp3 G β h F₂ := by
  unfold isingExp3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring


theorem isingExp3_const_mul (β h : ℝ) (r : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => r * F a b c) = r * isingExp3 G β h F := by
  unfold isingExp3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring


end Ising
end StatMech
