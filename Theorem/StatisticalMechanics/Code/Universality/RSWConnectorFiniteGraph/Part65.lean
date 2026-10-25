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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part86
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorReflectedDualConfig_eq_true_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorReflectedDualConfig gamma gamma' tau e = true ↔
      ∃ f : Ising.kwg_Edge
          (rlc_connectorAugmentedPlanarDomain gamma gamma'),
        f.1 ∉ (FK.openSub
          (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet ∧
        e.map Subtype.val =
          s(rlc_dualReflect (Ising.kwg_flankLeft
              (rlc_connectorAugmentedPlanarDomain gamma gamma') f),
            rlc_dualReflect (Ising.kwg_flankRight
              (rlc_connectorAugmentedPlanarDomain gamma gamma') f)) := by
  simp [rlc_connectorReflectedDualConfig]


theorem rlc_connectorReflectedDualConfig_open_preimage_mem_connector
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hopen : rlc_connectorReflectedDualConfig gamma gamma' tau e = true) :
    rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma' := by
  obtain ⟨⟨f, hfEdge⟩, hfClosed, he⟩ :=
    (rlc_connectorReflectedDualConfig_eq_true_iff
      gamma gamma' tau e).mp hopen
  induction f using Sym2.inductionOn with
  | _ x y =>
      have haug : (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp hfEdge
      change ((rlc_connectorFiniteGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y) at haug
      rcases haug with hfinite | htrace
      · have hpreimage : rlc_pimsEdgeEquiv (e.map Subtype.val) =
            s((x : RlcConnectorVertex n).val,
              (y : RlcConnectorVertex n).val) := by
          rw [he, rlc_pimsEdgeEquiv_reflected_mk_of_adj
            (Ising.kwg_flanks_adj _ ⟨s(x, y), hfEdge⟩),
            Ising.kwg_flanks_shared]
          rfl
        rw [hpreimage]
        exact hfinite.2
      · exfalso
        apply hfClosed
        apply (SimpleGraph.mem_edgeSet _).mpr
        rw [rlc_openSub_augmented_forceTrace]
        exact Or.inr htrace


theorem rlc_connectorReflectedDualConfig_le_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorReflectedDualConfig gamma gamma' tau <=
      rlc_connectorPIMSReflectedConfig gamma gamma' tau := by
  intro e
  by_cases hopen :
      rlc_connectorReflectedDualConfig gamma gamma' tau e = true
  · rw [hopen]
    obtain ⟨⟨f, hfEdge⟩, hfClosed, he⟩ :=
      (rlc_connectorReflectedDualConfig_eq_true_iff
        gamma gamma' tau e).mp hopen
    induction f using Sym2.inductionOn with
    | _ x y =>
        have haug :
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp hfEdge
        change ((rlc_connectorFiniteGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y) at haug
        rcases haug with hfinite | htrace
        · have htau : tau s(x, y) = false :=
            Bool.eq_false_of_not_eq_true fun htau => hfClosed <|
              (SimpleGraph.mem_edgeSet _).mpr <| by
                rw [rlc_openSub_augmented_forceTrace]
                exact Or.inl ⟨hfinite, htau⟩
          have hpreimage :
              rlc_pimsEdgeEquiv (e.map Subtype.val) =
                s(x.val, y.val) := by
            rw [he, rlc_pimsEdgeEquiv_reflected_mk_of_adj
              (Ising.kwg_flanks_adj _
                ⟨s(x, y), hfEdge⟩), Ising.kwg_flanks_shared]
            rfl
          have hlift :
              rlc_connectorEdgeLift gamma gamma'
                  s(x.val, y.val) hfinite.2 = s(x, y) := by
            apply rlc_sym2Map_subtypeVal_injective
            rw [rlc_connectorEdgeLift_map]
            rfl
          have hliftClosed :
              tau (rlc_connectorEdgeLift gamma gamma'
                s(x.val, y.val) hfinite.2) = false := by
            rw [hlift]
            exact htau
          have hpims :
              rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
            rw [rlc_connectorPIMSReflectedConfig_apply, hpreimage,
              rlc_connectorAmbientMixedConfig_connectorEdge
                gamma gamma' tau hfinite.2, hliftClosed]
            rfl
          rw [hpims]
        · exfalso
          apply hfClosed
          apply (SimpleGraph.mem_edgeSet _).mpr
          rw [rlc_openSub_augmented_forceTrace]
          exact Or.inr htrace
  · have hclosed :
        rlc_connectorReflectedDualConfig gamma gamma' tau e = false :=
      Bool.eq_false_of_not_eq_true hopen
    rw [hclosed]
    exact Bool.false_le _


theorem rlc_connectorReflectedDualConfig_le_PIMSCollared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorReflectedDualConfig gamma gamma' tau <=
      rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau := by
  intro e
  by_cases hopen :
      rlc_connectorReflectedDualConfig gamma gamma' tau e = true
  · rw [hopen]
    obtain ⟨⟨f, hfEdge⟩, hfClosed, he⟩ :=
      (rlc_connectorReflectedDualConfig_eq_true_iff
        gamma gamma' tau e).mp hopen
    induction f using Sym2.inductionOn with
    | _ x y =>
        have haug :
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp hfEdge
        change ((rlc_connectorFiniteGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y) at haug
        rcases haug with hfinite | htrace
        · have htau : tau s(x, y) = false :=
            Bool.eq_false_of_not_eq_true fun htau => hfClosed <|
              (SimpleGraph.mem_edgeSet _).mpr <| by
                rw [rlc_openSub_augmented_forceTrace]
                exact Or.inl ⟨hfinite, htau⟩
          have hpreimage :
              rlc_pimsEdgeEquiv (e.map Subtype.val) =
                s(x.val, y.val) := by
            rw [he, rlc_pimsEdgeEquiv_reflected_mk_of_adj
              (Ising.kwg_flanks_adj _
                ⟨s(x, y), hfEdge⟩), Ising.kwg_flanks_shared]
            rfl
          have hlift :
              rlc_connectorEdgeLift gamma gamma'
                  s(x.val, y.val) hfinite.2 = s(x, y) := by
            apply rlc_sym2Map_subtypeVal_injective
            rw [rlc_connectorEdgeLift_map]
            rfl
          have hliftClosed :
              tau (rlc_connectorEdgeLift gamma gamma'
                s(x.val, y.val) hfinite.2) = false := by
            rw [hlift]
            exact htau
          have hpims :
              rlc_connectorPIMSCollaredReflectedConfig
                  gamma gamma' tau e = true := by
            rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
              hpreimage,
              rlc_connectorAmbientCollaredConfig_connectorEdge
                gamma gamma' tau hfinite.2, hliftClosed]
            rfl
          rw [hpims]
        · exfalso
          apply hfClosed
          apply (SimpleGraph.mem_edgeSet _).mpr
          rw [rlc_openSub_augmented_forceTrace]
          exact Or.inr htrace
  · have hclosed :
        rlc_connectorReflectedDualConfig gamma gamma' tau e = false :=
      Bool.eq_false_of_not_eq_true hopen
    rw [hclosed]
    exact Bool.false_le _

theorem rlc_connectorForcedDualProb_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    0 <= rlc_connectorForcedDualProb gamma gamma' p q tau := by
  unfold rlc_connectorForcedDualProb
  exact div_nonneg
    (BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorAugmentedPlanarDomain gamma gamma')
      (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' tau)) hp hp1 hq).le
    (rlc_connectorForcedDualZ_pos gamma gamma' hp hp1 hq).le


theorem rlc_connectorForcedDualEventMass_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {A B : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
    (hAB : A ⊆ B) :
    rlc_connectorForcedDualEventMass gamma gamma' p q A <=
      rlc_connectorForcedDualEventMass gamma gamma' p q B := by
  unfold rlc_connectorForcedDualEventMass
  apply Finset.sum_le_sum
  intro tau _
  by_cases htau : tau ∈ A
  · rw [Set.indicator_of_mem htau, Set.indicator_of_mem (hAB htau)]
  · rw [Set.indicator_of_notMem htau]
    have hind : 0 <= B.indicator (fun _ => (1 : Real)) tau :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) tau
    simpa using mul_nonneg hind
      (rlc_connectorForcedDualProb_nonneg gamma gamma' hp hp1 hq tau)


theorem rlc_bcEventMass_separate_eq_forcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A =
      rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.dualParam p q) q A := by
  unfold FK.bcEventMass rlc_connectorForcedDualEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_separate_eq_forcedDualProb gamma gamma' tau hp hp1 hq]


theorem rlc_bcProb_separate_selfDual_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {q : Real} (hq : 0 < q) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q tau =
      rlc_connectorForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q tau := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  simpa only [BeffaraDC.selfDualPoint_is_fixed hq] using
    rlc_bcProb_separate_eq_forcedDualProb gamma gamma' tau hp hp1 hq

theorem rlc_bcEventMass_separate_selfDual_eq_forcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {q : Real} (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q A =
      rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q A := by
  unfold FK.bcEventMass rlc_connectorForcedDualEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_separate_selfDual_eq_forcedDualProb gamma gamma' tau hq]


theorem rlc_connectorComponentWiring_le_merged_of_oneAttachment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (hattach : RlcConnectorExteriorOneAttachment H) :
    rlc_connectorComponentWiring H ≤
      rlc_connectorMergedWiring gamma gamma' := by
  rw [rlc_connectorComponentWiring_eq_bot_of_oneAttachment H hattach]
  exact bot_le


theorem rlc_connectorPIMSCollaredInducedWiring_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorComponentWiring
        (rlc_connectorPIMSCollaredExteriorOpenGraph gamma gamma' tau) ≤
      rlc_connectorMergedWiring gamma gamma' :=
  rlc_connectorComponentWiring_le_merged_of_oneAttachment
    gamma gamma' _
      (rlc_connectorPIMSCollaredExterior_oneAttachment gamma gamma' tau)


end
end StatMech.Universality
