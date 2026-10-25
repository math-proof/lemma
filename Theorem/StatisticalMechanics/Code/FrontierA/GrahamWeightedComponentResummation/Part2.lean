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
import Def.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponentResummation.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamDisconnectedPairMass_eq_restrictedVacuumComponentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (g k l : V) :
    grahamDisconnectedPairMass G beta J g k l =
      grahamRestrictedVacuumComponentMass G beta J g k l := by
  unfold grahamDisconnectedPairMass grahamRestrictedVacuumComponentMass
  apply Finset.sum_congr rfl
  intro S hS
  rw [grahamAdmissibleComponentComplements, Finset.mem_filter] at hS
  exact grahamComponentPairMass_pair_eq_restricted_mul_vacuum
    G beta J S g k l hS.2.1 hS.2.2.1 hS.2.2.2


theorem graham_full_mul_vacuum_sub_disconnected_eq_gksDrop
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (g k l : V) :
    expectationJ G beta J {k, l} *
        (∑ S ∈ grahamAdmissibleComponentComplements g k l,
          grahamComponentPairMass G beta J S g ∅) -
      grahamDisconnectedPairMass G beta J g k l =
    ∑ S ∈ grahamAdmissibleComponentComplements g k l,
      grahamComponentPairMass G beta J S g ∅ *
        (expectationJ G beta J {k, l} -
          expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l}) := by
  rw [grahamDisconnectedPairMass_eq_restrictedVacuumComponentMass]
  unfold grahamRestrictedVacuumComponentMass
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring


theorem grahamComponentGKSDifference_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (S : Finset V) (k l : V) :
    0 <= expectationJ G beta J {k, l} -
      expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l} := by
  have hmono := expectationJ_couplingIn_le G beta J hbeta hJ S {k, l}
  linarith


theorem grahamComponentPairMass_vacuum_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (S : Finset V) (g : V) :
    0 <= grahamComponentPairMass G beta J S g ∅ := by
  unfold grahamComponentPairMass
  apply tsum_nonneg
  intro pq
  by_cases h1 : sources G (ofEdgeFun G pq.1) = ∅ <;>
    by_cases h2 : sources G (ofEdgeFun G pq.2) = ∅ <;>
    by_cases h3 : notConnComp G
      (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S <;>
    simp [h1, h2, h3]
  exact mul_nonneg
    (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G pq.1))
    (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G pq.2))


theorem grahamComponentGKSDrop_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (g k l : V) :
    0 <= ∑ S ∈ grahamAdmissibleComponentComplements g k l,
      grahamComponentPairMass G beta J S g ∅ *
        (expectationJ G beta J {k, l} -
          expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l}) := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg
    (grahamComponentPairMass_vacuum_nonneg G beta J hbeta hJ S g)
    (grahamComponentGKSDifference_nonneg G beta J hbeta hJ S k l)

end StatMech.FrontierA
