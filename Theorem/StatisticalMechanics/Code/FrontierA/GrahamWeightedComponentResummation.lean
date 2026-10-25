/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponentResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent.Part2
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentResummation
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamComponentPairMass_eq_gatedSourcePairSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V) (g : V)
    (A : Finset V) :
    grahamComponentPairMass G beta J S g A =
      gatedSourcePairSum G beta J A ∅
        (fun m => notConnComp G m g = S) := by
  unfold grahamComponentPairMass gatedSourcePairSum
  apply tsum_congr
  intro pq
  rw [ofEdgeFun_add]


theorem grahamComponentPairMass_pair_eq_restricted_mul_vacuum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (S : Finset V)
    (g k l : V) (hg : g ∉ S) (hk : k ∈ S) (hl : l ∈ S) :
    grahamComponentPairMass G beta J S g {k, l} =
      expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l} *
        grahamComponentPairMass G beta J S g ∅ := by
  unfold grahamComponentPairMass
  exact claim2_ising G beta J S g hg k l hk hl
    (ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta
      (StatMech.Sharpness.couplingIn J S)))


end StatMech.FrontierA
