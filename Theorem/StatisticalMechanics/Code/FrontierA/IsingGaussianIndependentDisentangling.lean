/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedEq22Refinement
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteTreeIndependentDisjointComponentMass_le_mixedDisconnection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) :
    finiteTreeIndependentDisjointComponentMass G beta J i j k l <=
      sourcePairDisconnSum G beta J {i, j} {k, l} i k *
        currentSum G beta J ∅ ^ 2 := by
  rw [finiteTree_mixedDisconnection_eq_componentReplacement
    G beta J hij hkl]
  rw [Finset.sum_mul]
  unfold finiteTreeIndependentDisjointComponentMass
  apply Finset.sum_le_sum
  intro S hS
  rw [grahamFirstAdmissibleComponentComplements,
    Finset.mem_filter] at hS
  have hfirst : 0 <= grahamFirstComponentFiber
      G beta J S i {i, j} ∅ :=
    gatedSourcePairSum_nonneg G beta J hbeta hJ {i, j} ∅
      (fun n => notConnComp G n i = S)
  have hconf := finiteTreeClusterConfinementMass_le
    G beta J hbeta hJ hkl S
  calc
    grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          finiteTreeClusterConfinementMass G beta J k l S
        <= grahamFirstComponentFiber G beta J S i {i, j} ∅ *
          (expectationJ G beta (couplingIn J S) {k, l} *
            currentSum G beta J ∅ ^ 2) :=
      mul_le_mul_of_nonneg_left hconf hfirst
    _ = (expectationJ G beta (couplingIn J S) {k, l} *
          grahamFirstComponentFiber G beta J S i {i, j} ∅) *
            currentSum G beta J ∅ ^ 2 := by ring

end StatMech.FrontierA
