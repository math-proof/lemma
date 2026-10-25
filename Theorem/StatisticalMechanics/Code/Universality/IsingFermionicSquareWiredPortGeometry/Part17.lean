/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part17


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredExpandedCyclePhaseSign
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.KWStraightLineCyclePhaseSign
      (fkIsingSquareWiredExpandedGraph n hn omega)
      (fkIsingSquareWiredExpandedEmbedding n hn omega) :=
  StatMech.FrontierA.kwStraightLineCyclePhaseSign_adaptive
    (fkIsingSquareWiredExpandedEmbedding n hn omega)


theorem fkIsingSquareWiredExpandedCycle_phase_eq_neg_one
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    StatMech.FrontierA.kwLoopPhaseProduct
        (fkIsingSquareWiredExpandedEmbedding n hn omega).turnPhase
        (StatMech.FrontierA.kwGraphCycleDartLoop p) = -1 :=
  fkIsingSquareWiredExpandedCyclePhaseSign n hn omega p hp


theorem fkIsingSquareWiredExpandedCycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) (turn : Int)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      Complex.exp
          (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) =
        StatMech.FrontierA.kwLoopPhaseProduct
          (fkIsingSquareWiredExpandedEmbedding n hn omega).turnPhase
          (StatMech.FrontierA.kwGraphCycleDartLoop p)) :
    turn ≡ 8 [ZMOD 16] := by
  apply int_eighth_turn_mod_sixteen_of_exp_eq_neg_one
  rw [hphase]
  exact fkIsingSquareWiredExpandedCycle_phase_eq_neg_one n hn omega p hp


theorem fkIsingSquareWired_one_visit_west_carrierCycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
          s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
            (.dart (e, .east)) (.dart (e, .north)))
    (hr : r.IsPath) :
    ∃ p : (fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).Walk (.dart (e, .east)) (.dart (e, .east)),
      p.IsCycle ∧ p.support =
        (.dart (e, .east) : FKIsingSquareWiredCarrier n) :: r.reverse.support := by
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let removed : Set (Sym2 (FKIsingSquareWiredCarrier n)) :=
    {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
      s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}
  have hEN : H.Adj (.dart (e, .east)) (.dart (e, .north)) := by
    exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate])
  let q : H.Walk (.dart (e, .north)) (.dart (e, .east)) :=
    r.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
  let p : H.Walk (.dart (e, .east)) (.dart (e, .east)) :=
    SimpleGraph.Walk.cons hEN q
  refine ⟨p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · exact hr.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
    · intro hedge
      have hedge' : s((.dart (e, .east) : FKIsingSquareWiredCarrier n),
          .dart (e, .north)) ∈ r.reverse.edges := by
        simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
      have hdeleted := r.reverse.edges_subset_edgeSet hedge'
      rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
      exact hdeleted.2 (by simp [removed])
  · simp [p, q, SimpleGraph.Walk.support_mapLe_eq_support]


theorem fkIsingSquareWired_one_visit_east_carrierCycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
          s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
            (.dart (e, .west)) (.dart (e, .south)))
    (hr : r.IsPath) :
    ∃ p : (fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).Walk (.dart (e, .west)) (.dart (e, .west)),
      p.IsCycle ∧ p.support =
        (.dart (e, .west) : FKIsingSquareWiredCarrier n) :: r.reverse.support := by
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let removed : Set (Sym2 (FKIsingSquareWiredCarrier n)) :=
    {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
      s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}
  have hWS : H.Adj (.dart (e, .west)) (.dart (e, .south)) := by
    exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate])
  let q : H.Walk (.dart (e, .south)) (.dart (e, .west)) :=
    r.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
  let p : H.Walk (.dart (e, .west)) (.dart (e, .west)) :=
    SimpleGraph.Walk.cons hWS q
  refine ⟨p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · exact hr.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
    · intro hedge
      have hedge' : s((.dart (e, .west) : FKIsingSquareWiredCarrier n),
          .dart (e, .south)) ∈ r.reverse.edges := by
        simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
      have hdeleted := r.reverse.edges_subset_edgeSet hedge'
      rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
      exact hdeleted.2 (by simp [removed])
  · simp [p, q, SimpleGraph.Walk.support_mapLe_eq_support]


end
end StatMech.Universality
