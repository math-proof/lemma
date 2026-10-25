/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteTreeSafeRegionFiber_factor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V)
    (A C : Finset V) (hA : A ⊆ T) (hC : C ⊆ T) :
    finiteTreeSafeRegionFiber G beta J roots T A C =
      currentSum G beta (couplingIn J T) A *
        currentSum G beta (couplingIn J T) C *
          finiteTreeSafeRegionContext G beta J roots T := by
  unfold finiteTreeSafeRegionFiber finiteTreeSafeRegionContext
  have hcongr : ∀ n n' : Current V,
      (∀ e ∈ G.edgeFinset, ¬ edgeInside T e -> n e = n' e) ->
      (finiteTreeSafeRegion G n roots = T ↔
        finiteTreeSafeRegion G n' roots = T) := by
    intro n n' hagree
    constructor
    · intro hn
      exact finiteTreeSafeRegion_congr G n n' roots T hn hagree
    · intro hn'
      exact finiteTreeSafeRegion_congr G n' n roots T hn'
        (fun e he hnot => (hagree e he hnot).symm)
  have hfactor := gatedSourcePairSum_factor G beta J T
    (fun n => finiteTreeSafeRegion G n roots = T)
    (fun n hn => finiteTreeSafeRegion_noCrossing G n roots T hn)
    hcongr A ∅ C ∅ hA (by simp) hC (by simp)
  have hA0 : symmDiff A (∅ : Finset V) = A := by
    ext x
    simp [Finset.mem_symmDiff]
  have hC0 : symmDiff C (∅ : Finset V) = C := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hA0, hC0] at hfactor
  exact hfactor

theorem finiteTreeSafeRegionFiber_sourceReplacement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V)
    (A : Finset V) (hA : A ⊆ T) :
    finiteTreeSafeRegionFiber G beta J roots T A ∅ =
      expectationJ G beta (couplingIn J T) A *
        finiteTreeSafeRegionFiber G beta J roots T ∅ ∅ := by
  rw [finiteTreeSafeRegionFiber_factor G beta J roots T A ∅ hA (by simp),
    finiteTreeSafeRegionFiber_factor G beta J roots T ∅ ∅ (by simp) (by simp),
    StatMech.Ising.acr_eq15_insertion' G beta (couplingIn J T) A]
  ring

theorem finiteTreeSafeRegionFiber_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (roots T A C : Finset V) :
    0 <= finiteTreeSafeRegionFiber G beta J roots T A C := by
  exact gatedSourcePairSum_nonneg G beta J hbeta hJ A C
    (fun n => finiteTreeSafeRegion G n roots = T)


end StatMech.FrontierA
