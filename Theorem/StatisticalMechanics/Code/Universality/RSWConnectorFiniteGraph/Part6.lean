/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_openSub_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  simp only [FK.openSub_adj, rlc_connectorAugmentedPlanarDomain,
    SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hfinite | htrace, hopen⟩
    · left
      refine ⟨hfinite, ?_⟩
      have hnot : s(x, y) ∉
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        intro hmem
        exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma'
          hfinite ((SimpleGraph.mem_edgeSet
            (rlc_connectorTraceWiring gamma gamma')).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
      change (if s(x, y) ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
          then true else tau s(x, y)) = true at hopen
      rw [if_neg hnot] at hopen
      exact hopen
    · exact Or.inr htrace
  · rintro (⟨hfinite, hopen⟩ | htrace)
    · refine ⟨Or.inl hfinite, ?_⟩
      have hnot : s(x, y) ∉
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        intro hmem
        exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma'
          hfinite ((SimpleGraph.mem_edgeSet
            (rlc_connectorTraceWiring gamma gamma')).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
      change (if s(x, y) ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
          then true else tau s(x, y)) = true
      rw [if_neg hnot]
      exact hopen
    · refine ⟨Or.inr htrace, ?_⟩
      have hmem : s(x, y) ∈
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        exact SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.mem_edgeSet
            (rlc_connectorTraceWiring gamma gamma')).mpr htrace)
      change (if s(x, y) ∈
        (rlc_connectorTraceWiring gamma gamma').edgeFinset
          then true else tau s(x, y)) = true
      rw [if_pos hmem]


theorem rlc_numClusters_augmented_forceTrace_eq_traceBC {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClusters (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') tau := by
  let A := FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
    (rlc_connectorForceTraceConfig gamma gamma' tau)
  let B := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
    rlc_connectorTraceWiring gamma gamma'
  have hAB : A = B := rlc_openSub_augmented_forceTrace gamma gamma' tau
  have htypes : A.ConnectedComponent = B.ConnectedComponent :=
    congrArg (fun H : SimpleGraph (RlcConnectorVertex n) =>
      H.ConnectedComponent) hAB
  unfold FK.numClusters FK.numClustersBC
  calc
    Fintype.card A.ConnectedComponent = Nat.card A.ConnectedComponent :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card B.ConnectedComponent :=
      Nat.card_congr (Equiv.cast htypes)


theorem rlc_connectorForced_clusterEuler {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
    let K := FK.openSub P.G
      (rlc_connectorForceTraceConfig gamma gamma' tau)
    Nat.card P.V +
        Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent =
      K.edgeSet.ncard +
        FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') tau + 1 := by
  dsimp only
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma' tau)
  have heuler := BeffaraDC.pfd_clusterEuler P K
    (FK.openSub_le P.G (rlc_connectorForceTraceConfig gamma gamma' tau))
  have hk : Nat.card K.ConnectedComponent =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') tau := by
    calc
      Nat.card K.ConnectedComponent = Fintype.card K.ConnectedComponent :=
        Nat.card_eq_fintype_card
      _ = FK.numClusters P.G
          (rlc_connectorForceTraceConfig gamma gamma' tau) := rfl
      _ = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorTraceWiring gamma gamma') tau :=
        rlc_numClusters_augmented_forceTrace_eq_traceBC gamma gamma' tau
      _ = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') tau :=
        rlc_numClustersBC_traceWiring_eq_separateWiring gamma gamma' tau
  simpa only [P, K, hk] using heuler


theorem rlc_edgeProduct_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.edgeProduct (rlc_connectorAugmentedPlanarDomain gamma gamma').G p
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.edgeProduct (rlc_connectorFiniteGraph gamma gamma') p tau := by
  classical
  let G := rlc_connectorFiniteGraph gamma gamma'
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
        exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma' hG hT
  have hGprod :
      (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) =
        ∏ e ∈ G.edgeFinset, if tau e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e heG
    have hnot : e ∉ T.edgeFinset := Finset.disjoint_left.mp hd heG
    simp [rlc_connectorForceTraceConfig, T, hnot]
  have hTprod :
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) = p ^ T.edgeFinset.card := by
    calc
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) = ∏ _e ∈ T.edgeFinset, p := by
        apply Finset.prod_congr rfl
        intro e heT
        have hforce : rlc_connectorForceTraceConfig gamma gamma' tau e = true := by
          simp [rlc_connectorForceTraceConfig, T, heT]
        simp only [hforce, if_true]
      _ = p ^ T.edgeFinset.card := by simp
  unfold FK.edgeProduct
  have hEdges :
      (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset =
        G.edgeFinset ∪ T.edgeFinset := by
    simp [rlc_connectorAugmentedPlanarDomain, G, T]
  rw [hEdges]
  calc
    (∏ e ∈ G.edgeFinset ∪ T.edgeFinset,
        if rlc_connectorForceTraceConfig gamma gamma' tau e
          then p else 1 - p) =
        (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p) *
        ∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' tau e
            then p else 1 - p := Finset.prod_union hd
    _ = (∏ e ∈ G.edgeFinset, if tau e then p else 1 - p) *
        p ^ T.edgeFinset.card := by rw [hGprod, hTprod]
    _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        ∏ e ∈ (rlc_connectorFiniteGraph gamma gamma').edgeFinset,
          if tau e then p else 1 - p := by simp only [G, T, mul_comm]


theorem rlc_fkWeight_augmented_forceTrace_eq_separateBC {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.fkWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G p q
        (rlc_connectorForceTraceConfig gamma gamma' tau) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q tau := by
  unfold FK.fkWeight FK.bcWeight
  rw [rlc_edgeProduct_augmented_forceTrace,
    rlc_numClusters_augmented_forceTrace_eq_traceBC,
    rlc_numClustersBC_traceWiring_eq_separateWiring]
  ring


theorem rlc_connectorForced_weight_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
    let forced := rlc_connectorForceTraceConfig gamma gamma' tau
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcWeight (rlc_connectorFiniteGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q tau *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          BeffaraDC.pfdDualWeight P (BeffaraDC.dualParam p q) q
            (FK.openSub P.G forced) := by
  dsimp only
  rw [← rlc_fkWeight_augmented_forceTrace_eq_separateBC]
  exact BeffaraDC.pfd_fkWeight_duality
    (rlc_connectorAugmentedPlanarDomain gamma gamma')
    (rlc_connectorForceTraceConfig gamma gamma' tau) hp hp1 hq


end
end StatMech.Universality
