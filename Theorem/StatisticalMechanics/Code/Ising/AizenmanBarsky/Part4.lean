/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean -/

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
import Def.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part4
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem expectation_negHam_cov_expand (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s * negHam G h s)
        - isingExpectation G β h f * isingExpectation G β h (negHam G h)
      = (∑ e ∈ G.edgeFinset,
          (isingExpectation G β h (fun s => f s * bond s e)
            - isingExpectation G β h f * isingExpectation G β h (fun s => bond s e)))
        + h * ∑ x,
          (isingExpectation G β h (fun s => f s * spin s x)
            - isingExpectation G β h f * isingExpectation G β h (fun s => spin s x)) := by
  
  have hnum : isingExpectation G β h (fun s => f s * negHam G h s)
      = (∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => f s * bond s e))
        + h * ∑ x, isingExpectation G β h (fun s => f s * spin s x) := by
    have step1 : (fun s => f s * negHam G h s)
        = (fun s => (fun s => f s * ∑ e ∈ G.edgeFinset, bond s e) s
              + (fun s => h * (f s * ∑ x, spin s x)) s) := by
      funext s; unfold negHam; ring
    rw [step1, expectation_add]
    congr 1
    · have hbr : (fun s => f s * ∑ e ∈ G.edgeFinset, bond s e)
          = (fun cfg => ∑ e ∈ G.edgeFinset, (fun e s => f s * bond s e) e cfg) := by
        funext s; rw [Finset.mul_sum]
      rw [hbr, expectation_sum]
    · rw [expectation_const_mul]
      congr 1
      have hsp : (fun s => f s * ∑ x, spin s x)
          = (fun cfg => ∑ x, (fun x s => f s * spin s x) x cfg) := by
        funext s; rw [Finset.mul_sum]
      rw [hsp, expectation_sum]
  
  have hZ : isingExpectation G β h (negHam G h)
      = (∑ e ∈ G.edgeFinset, isingExpectation G β h (fun s => bond s e))
        + h * ∑ x, isingExpectation G β h (fun s => spin s x) := by
    have step1 : (negHam G h)
        = (fun s => (fun s => ∑ e ∈ G.edgeFinset, bond s e) s
              + (fun s => h * (∑ x, spin s x)) s) := by
      funext s; unfold negHam; ring
    rw [step1, expectation_add]
    congr 1
    · have hbr : (fun s : ConfigSpace V => ∑ e ∈ G.edgeFinset, bond s e)
          = (fun cfg => ∑ e ∈ G.edgeFinset, (fun e s => bond s e) e cfg) := rfl
      rw [hbr, expectation_sum]
    · rw [expectation_const_mul]
      congr 1
      have hsp : (fun s : ConfigSpace V => ∑ x, spin s x)
          = (fun cfg => ∑ x, (fun x s => spin s x) x cfg) := rfl
      rw [hsp, expectation_sum]
  rw [hnum, hZ]
  
  set X := isingExpectation G β h f with hX
  
  have hbond : (∑ e ∈ G.edgeFinset,
        ((isingExpectation G β h fun s => f s * bond s e)
          - X * isingExpectation G β h fun s => bond s e))
      = (∑ e ∈ G.edgeFinset, isingExpectation G β h fun s => f s * bond s e)
        - X * ∑ e ∈ G.edgeFinset, isingExpectation G β h fun s => bond s e := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  
  have hfield : (∑ x, ((isingExpectation G β h fun s => f s * spin s x)
          - X * isingExpectation G β h fun s => spin s x))
      = (∑ x, isingExpectation G β h fun s => f s * spin s x)
        - X * ∑ x, isingExpectation G β h fun s => spin s x := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hbond, hfield]
  ring


theorem deriv_magnetization_beta_eq (β h : ℝ) (o : V) :
    deriv (fun β => isingExpectation G β h (fun s => spin s o)) β
      = bondEnergySusceptibility G β h o + h * susceptibility G β h o := by
  rw [(hasDerivAt_expectation_beta G β h (fun s => spin s o)).deriv]
  rw [expectation_negHam_cov_expand]
  unfold bondEnergySusceptibility susceptibility cov2
  congr 1
  
  apply Finset.sum_congr rfl
  intro e _
  induction e with
  | h x y =>
    rw [cov3sym_mk]; rfl


end Ising
end StatMech
