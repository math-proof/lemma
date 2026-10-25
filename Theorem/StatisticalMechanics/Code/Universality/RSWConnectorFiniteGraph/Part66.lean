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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part36
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorMergedWiring_le_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorMergedWiring gamma gamma' ≤
      rlc_connectorMergedClique gamma gamma' := by
  intro x y hxy
  rw [rlc_connectorMergedClique, Lattice.boundaryCliqueGraph_adj]
  rcases hxy with hsep | hedge
  · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
    rcases hsep with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact ⟨hright.1, Or.inl hright.2.1, Or.inl hright.2.2⟩
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact ⟨hleft.1, Or.inr hleft.2.1, Or.inr hleft.2.2⟩
  · rw [SimpleGraph.edge_adj] at hedge
    rcases hedge with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hne⟩
    · exact ⟨hne, Or.inl (rlc_connectorRightAnchor_onRight gamma),
          Or.inr (rlc_connectorLeftAnchor_onLeft gamma')⟩
    · exact ⟨hne, Or.inr (rlc_connectorLeftAnchor_onLeft gamma'),
          Or.inl (rlc_connectorRightAnchor_onRight gamma)⟩


theorem rlc_connectorMergedWiring_reachable_onEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hx : rlc_connectorOnEither gamma gamma' x)
    (hy : rlc_connectorOnEither gamma gamma' y) :
    (rlc_connectorMergedWiring gamma gamma').Reachable x y := by
  have hanchor : (rlc_connectorMergedWiring gamma gamma').Reachable
      (rlc_connectorRightAnchor gamma)
      (rlc_connectorLeftAnchor gamma') := by
    by_cases h : rlc_connectorRightAnchor gamma =
        rlc_connectorLeftAnchor gamma'
    · rw [h]
    · exact (show (rlc_connectorMergedWiring gamma gamma').Adj
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') from Or.inr <|
            (SimpleGraph.edge_adj _ _ _ _).2
              ⟨Or.inl ⟨rfl, rfl⟩, h⟩).reachable
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (rlc_connectorTraceWiring_reachable_right gamma gamma' hx hy).mono
      ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
        le_sup_left)
  · exact ((rlc_connectorTraceWiring_reachable_right gamma gamma' hx
      (rlc_connectorRightAnchor_onRight gamma)).mono
        ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
          le_sup_left)).trans <|
      (hanchor.trans <|
        (rlc_connectorTraceWiring_reachable_left gamma gamma'
          (rlc_connectorLeftAnchor_onLeft gamma') hy).mono
            ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
              le_sup_left))
  · exact ((rlc_connectorTraceWiring_reachable_left gamma gamma' hx
      (rlc_connectorLeftAnchor_onLeft gamma')).mono
        ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
          le_sup_left)).trans <|
      (hanchor.symm.trans <|
        (rlc_connectorTraceWiring_reachable_right gamma gamma'
          (rlc_connectorRightAnchor_onRight gamma) hy).mono
            ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
              le_sup_left))
  · exact (rlc_connectorTraceWiring_reachable_left gamma gamma' hx hy).mono
      ((rlc_connectorTraceWiring_le_separateWiring gamma gamma').trans
        le_sup_left)


theorem rlc_connectorMergedWiring_reachable_iff_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (x y : RlcConnectorVertex n) :
    (H ⊔ rlc_connectorMergedWiring gamma gamma').Reachable x y ↔
      (H ⊔ rlc_connectorMergedClique gamma gamma').Reachable x y := by
  constructor
  · exact Reachable.mono (sup_le_sup_left
      (rlc_connectorMergedWiring_le_mergedClique gamma gamma') H)
  · intro hxy
    apply rlc_reachable_of_step_reachable
      (G := H ⊔ rlc_connectorMergedClique gamma gamma')
      (K := H ⊔ rlc_connectorMergedWiring gamma gamma') ?_ hxy
    intro u v huv
    rcases huv with hH | hclique
    · exact (show (H ⊔ rlc_connectorMergedWiring gamma gamma').Adj u v
        from Or.inl hH).reachable
    · rw [rlc_connectorMergedClique,
        Lattice.boundaryCliqueGraph_adj] at hclique
      exact (rlc_connectorMergedWiring_reachable_onEither
        gamma gamma' hclique.2.1 hclique.2.2).mono le_sup_right


theorem rlc_numClustersBC_mergedWiring_eq_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') tau =
      FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedClique gamma gamma') tau := by
  unfold FK.numClustersBC
  apply Nat.card_congr
  let A := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
    rlc_connectorMergedWiring gamma gamma'
  let B := FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau ⊔
    rlc_connectorMergedClique gamma gamma'
  apply Equiv.ofBijective (fun C : A.ConnectedComponent =>
    B.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hB : B.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hA : A.Reachable C.out D.out :=
      (rlc_connectorMergedWiring_reachable_iff_mergedClique
        gamma gamma' _ C.out D.out).mpr hB
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hA
  · intro D
    let C := A.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hA : A.Reachable C.out D.out := ConnectedComponent.exact C.out_eq
    exact (rlc_connectorMergedWiring_reachable_iff_mergedClique
      gamma gamma' _ C.out D.out).mp hA


theorem rlc_bcProb_mergedWiring_eq_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') p q tau =
      FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedClique gamma gamma') p q tau := by
  unfold FK.bcProb FK.bcZ FK.bcWeight
  simp_rw [rlc_numClustersBC_mergedWiring_eq_mergedClique]

theorem rlc_bcEventMass_mergedWiring_eq_mergedClique {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) :
    FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') p q A =
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedClique gamma gamma') p q A := by
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro tau _
  rw [rlc_bcProb_mergedWiring_eq_mergedClique]


theorem rlc_connectorForcedDualEventMass_compl_le_merged_of_equiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ tau, tau ∉ A → D tau ∈ A)
    (hprob : ∀ tau,
      rlc_connectorForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q tau <=
        FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D tau)) :
    rlc_connectorForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q Aᶜ <=
      FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q A := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_connectorForcedDualEventMass FK.bcEventMass
  rw [← Equiv.sum_comp D (fun eta :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
      A.indicator (fun _ => (1 : Real)) eta *
        FK.bcProb (rlc_connectorFiniteGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta)]
  apply Finset.sum_le_sum
  intro tau _
  by_cases htau : tau ∈ A
  · rw [Set.indicator_of_notMem (by simpa using htau)]
    simp only [zero_mul]
    exact mul_nonneg (by
      by_cases hD : D tau ∈ A <;> simp [hD])
      (FK.bcProb_nonneg (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 (D tau))
  · rw [Set.indicator_of_mem (by simpa using htau),
      Set.indicator_of_mem (hfailure tau htau)]
    simpa using hprob tau


end
end StatMech.Universality
