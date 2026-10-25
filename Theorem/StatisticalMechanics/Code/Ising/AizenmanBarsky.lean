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
import Def.StatisticalMechanics.Code.Ising.AizenmanBarsky
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem hasDerivAt_isingWeight_beta (β h : ℝ) (s : ConfigSpace V) :
    HasDerivAt (fun β => isingWeight G β h s)
      (isingWeight G β h s * negHam G h s) β := by
  unfold isingWeight hamiltonian negHam
  set E := ∑ e ∈ G.edgeFinset, bond s e with hE
  set M := ∑ x, spin s x with hM
  have hrw : (fun β => Real.exp (-β * (-E - h * M)))
      = (fun β => Real.exp (β * (E + h * M))) := by funext β; congr 1; ring
  rw [hrw]
  have hlin : HasDerivAt (fun β : ℝ => β * (E + h * M)) (E + h * M) β := by
    simpa using (hasDerivAt_id β).mul_const (E + h * M)
  have hcomp := (Real.hasDerivAt_exp (β * (E + h * M))).comp β hlin
  have hval : Real.exp (-β * (-E - h * M)) = Real.exp (β * (E + h * M)) := by
    congr 1; ring
  rw [hval]; exact hcomp


theorem hasDerivAt_num_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) β := by
  have hpt : (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s)
      = ∑ s : ConfigSpace V, (fun β => f s * isingWeight G β h s) := by rw [Finset.sum_fn]
  rw [hpt]
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_isingWeight_beta G β h s).const_mul (f s))


theorem hasDerivAt_isingZ_beta (β h : ℝ) :
    HasDerivAt (fun β => isingZ G β h)
      (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s) β := by
  have h1 := hasDerivAt_num_beta G β h (fun _ => 1)
  simp only [one_mul] at h1
  exact h1


theorem hasDerivAt_expectation_beta (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun β => isingExpectation G β h f)
      (isingExpectation G β h (fun s => f s * negHam G h s)
            - isingExpectation G β h f * isingExpectation G β h (negHam G h)) β := by
  have hN := hasDerivAt_num_beta G β h f
  have hZ := hasDerivAt_isingZ_beta G β h
  have hZne : isingZ G β h ≠ 0 := isingZ_ne_zero G β h
  have hfun : (fun β => isingExpectation G β h f)
      = (fun β => (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h) := by
    funext β; exact expectation_eq_div G β h f
  rw [hfun]
  have hdiv := hN.div hZ hZne
  have e1 : isingExpectation G β h (fun s => f s * negHam G h s)
      = (∑ s : ConfigSpace V, (f s * negHam G h s) * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h _
  have e2 : isingExpectation G β h f
      = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h f
  have e3 : isingExpectation G β h (negHam G h)
      = (∑ s : ConfigSpace V, negHam G h s * isingWeight G β h s) / isingZ G β h :=
    expectation_eq_div G β h (negHam G h)
  set Z := isingZ G β h with hZdef
  set A := ∑ s : ConfigSpace V, (f s * negHam G h s) * isingWeight G β h s with hAdef
  set B := ∑ s : ConfigSpace V, f s * isingWeight G β h s with hBdef
  set C := ∑ s : ConfigSpace V, negHam G h s * isingWeight G β h s with hCdef
  have hN'eq :
      (∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) = A := by
    rw [hAdef]; apply Finset.sum_congr rfl; intro s _; ring
  have hZ'eq :
      (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s) = C := by
    rw [hCdef]; apply Finset.sum_congr rfl; intro s _; ring
  rw [e1, e2, e3]
  have hval : (A / Z - B / Z * (C / Z))
      = ((∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) * Z
          - B * (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s)) / Z ^ 2 := by
    rw [hN'eq, hZ'eq]; field_simp
  rw [hval]
  exact hdiv


theorem expectation_add (β h : ℝ) (f g : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => f s + g s)
      = isingExpectation G β h f + isingExpectation G β h g := by
  unfold isingExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _; ring


theorem expectation_const_mul (β h : ℝ) (c : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h (fun s => c * f s) = c * isingExpectation G β h f := by
  unfold isingExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _; ring


end Ising
end StatMech
