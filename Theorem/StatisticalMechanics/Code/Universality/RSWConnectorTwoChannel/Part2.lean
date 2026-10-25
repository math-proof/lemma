/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorTwoChannelAugmentedGraph_eq_closure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G =
      rlc_connectorCentralFaceClosureGraph gamma gamma' := by
  exact (rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace
    gamma gamma').symm


theorem rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') rho =
      FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') rho := by
  unfold FK.numClustersBC
  exact Nat.card_congr (rlc_connectorTraceComponentEquiv gamma gamma'
    (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho))

theorem rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q rho =
      FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho := by
  unfold FK.bcWeight
  rw [rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring]

theorem rlc_twoChannel_bcZ_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q =
      FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q := by
  unfold FK.bcZ
  apply Finset.sum_congr rfl
  intro rho _
  exact rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring
    gamma gamma' p q rho

theorem rlc_twoChannel_bcProb_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q rho =
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho := by
  unfold FK.bcProb
  rw [rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring,
    rlc_twoChannel_bcZ_traceWiring_eq_separateWiring]

theorem rlc_twoChannel_bcEventMass_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q A =
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A := by
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro rho _
  rw [rlc_twoChannel_bcProb_traceWiring_eq_separateWiring]


theorem rlc_openSub_twoChannelAugmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain
          gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  simp only [FK.openSub_adj,
    rlc_connectorTwoChannelAugmentedPlanarDomain, SimpleGraph.sup_adj]
  by_cases htrace :
      (rlc_connectorTraceWiring gamma gamma').Adj x y
  · simp [rlc_connectorForceTraceConfig, htrace]
  · simp [rlc_connectorForceTraceConfig, htrace]

theorem rlc_connectorTwoChannelGraph_adj_not_traceWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y) :
    ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y :=
  hxy.2

theorem rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClusters (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') rho := by
  let A := FK.openSub
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
    (rlc_connectorForceTraceConfig gamma gamma' rho)
  let B := FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
    rlc_connectorTraceWiring gamma gamma'
  have hAB : A = B :=
    rlc_openSub_twoChannelAugmented_forceTrace gamma gamma' rho
  have htypes : A.ConnectedComponent = B.ConnectedComponent :=
    congrArg (fun H : SimpleGraph (RlcConnectorVertex n) =>
      H.ConnectedComponent) hAB
  unfold FK.numClusters FK.numClustersBC
  calc
    Fintype.card A.ConnectedComponent = Nat.card A.ConnectedComponent :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card B.ConnectedComponent :=
      Nat.card_congr (Equiv.cast htypes)

theorem rlc_twoChannel_edgeProduct_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.edgeProduct (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G p
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') p rho := by
  classical
  let G := rlc_connectorTwoChannelGraph gamma gamma'
  let T := rlc_connectorTraceWiring gamma gamma'
  have hd : Disjoint G.edgeFinset T.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heG heT
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hG : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp
          (SimpleGraph.mem_edgeFinset.mp heG)
        have hT : T.Adj x y := (SimpleGraph.mem_edgeSet T).mp
          (SimpleGraph.mem_edgeFinset.mp heT)
        exact rlc_connectorTwoChannelGraph_adj_not_traceWiring
          gamma gamma' hG hT
  have hGprod :
      (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) =
        ∏ e ∈ G.edgeFinset, if rho e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e heG
    have hnot : e ∉ T.edgeFinset := Finset.disjoint_left.mp hd heG
    simp [rlc_connectorForceTraceConfig, T, hnot]
  have hTprod :
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) = p ^ T.edgeFinset.card := by
    calc
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) = ∏ _e ∈ T.edgeFinset, p := by
        apply Finset.prod_congr rfl
        intro e heT
        simp [rlc_connectorForceTraceConfig, T, heT]
      _ = p ^ T.edgeFinset.card := by simp
  unfold FK.edgeProduct
  have hEdges :
      (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G.edgeFinset = G.edgeFinset ∪ T.edgeFinset := by
    simp [rlc_connectorTwoChannelAugmentedPlanarDomain, G, T]
  rw [hEdges]
  calc
    (∏ e ∈ G.edgeFinset ∪ T.edgeFinset,
        if rlc_connectorForceTraceConfig gamma gamma' rho e
          then p else 1 - p) =
        (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) *
        ∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p := Finset.prod_union hd
    _ = (∏ e ∈ G.edgeFinset, if rho e then p else 1 - p) *
        p ^ T.edgeFinset.card := by rw [hGprod, hTprod]
    _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        ∏ e ∈ (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset,
          if rho e then p else 1 - p := by
      simp only [G, T, mul_comm]


theorem rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.fkWeight (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G p q
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q rho := by
  unfold FK.fkWeight FK.bcWeight
  rw [rlc_twoChannel_edgeProduct_augmented_forceTrace,
    rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC,
    rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring]
  ring

theorem rlc_twoChannelForced_weight_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q rho *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          BeffaraDC.pfdDualWeight P (BeffaraDC.dualParam p q) q
            (FK.openSub P.G
              (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
  dsimp only
  rw [← rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC]
  exact BeffaraDC.pfd_fkWeight_duality
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
    (rlc_connectorForceTraceConfig gamma gamma' rho) hp hp1 hq

end
end StatMech.Universality
