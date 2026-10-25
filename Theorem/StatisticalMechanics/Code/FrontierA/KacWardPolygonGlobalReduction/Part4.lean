/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part3
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


theorem KWStraightLineCycleTurning.phaseProduct_eq_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hphase : embedding.turnPhase = fun dart next ↦
      kwAngleTurnPhase (embedding.dartAngle dart) (embedding.dartAngle next) := by
    funext dart next
    rw [← embedding.principalPhase_eq_turnPhase]
    rfl
  rw [hphase]
  exact kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn
    embedding.dartAngle (kwGraphCycleDartLoop p) (hturning p hp)


theorem KWStraightLineCycleOddTurning.phaseProduct_eq_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleOddTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hphase : embedding.turnPhase = fun dart next ↦
      kwAngleTurnPhase (embedding.dartAngle dart) (embedding.dartAngle next) := by
    funext dart next
    rw [← embedding.principalPhase_eq_turnPhase]
    rfl
  obtain ⟨winding, hsum, hodd⟩ := hturning p hp
  rw [hphase]
  exact kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding
    embedding.dartAngle (kwGraphCycleDartLoop p) winding hsum hodd

theorem KWStraightLineCycleOddTurning.toPhaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleOddTurning G embedding) :
    KWStraightLineCyclePhaseSign G embedding := by
  intro root p hp
  exact hturning.phaseProduct_eq_neg_one G embedding p hp

theorem KWStraightLineCyclePhaseSign.toOddTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hsign : KWStraightLineCyclePhaseSign G embedding) :
    KWStraightLineCycleOddTurning G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  obtain ⟨winding, hturn⟩ := kw_totalPrincipalTurn_eq_int_mul_two_pi
    embedding.dartAngle (kwGraphCycleDartLoop p)
  have hphaseEq : embedding.turnPhase = fun dart next ↦
      kwAngleTurnPhase (embedding.dartAngle dart) (embedding.dartAngle next) := by
    funext dart next
    rw [← embedding.principalPhase_eq_turnPhase]
    rfl
  have hphase : kwLoopPhaseProduct
      (fun dart next ↦ kwAngleTurnPhase
        (embedding.dartAngle dart) (embedding.dartAngle next))
      (kwGraphCycleDartLoop p) = -1 := by
    rw [← hphaseEq]
    exact hsign p hp
  exact ⟨winding, hturn,
    kw_odd_winding_of_angleTurnPhase_eq_neg_one
      embedding.dartAngle (kwGraphCycleDartLoop p) winding hturn hphase⟩

theorem kw_straightLineCycleOddTurning_iff_phaseSign
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWStraightLineCycleOddTurning G embedding ↔
      KWStraightLineCyclePhaseSign G embedding :=
  ⟨fun h ↦ h.toPhaseSign G embedding,
    fun h ↦ h.toOddTurning G embedding⟩


theorem KWStraightLineCycleTurning.toOddTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hturning : KWStraightLineCycleTurning G embedding) :
    KWStraightLineCycleOddTurning G embedding := by
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rcases hturning p hp with hpos | hneg
  · exact ⟨1, by simpa using hpos, by norm_num⟩
  · refine ⟨-1, ?_, by norm_num⟩
    simpa using hneg


theorem kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleOddTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwGraphFormalLogCoeff G embedding.turnPhase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  exact kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one
    G embedding hdeg p hp
      (hturning.phaseProduct_eq_neg_one G embedding p hp)


theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_oddCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleOddTurning G embedding) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G := by
  exact kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff
    G embedding hdeg
      (kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning
        G embedding hdeg hturning)


theorem kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwGraphFormalLogCoeff G embedding.turnPhase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  exact kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one
    G embedding hdeg p hp
      (hturning.phaseProduct_eq_neg_one G embedding p hp)


theorem kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding) :
    kwGraphFormalRoot G embedding.turnPhase =
      kwGraphFormalEvenPolynomial G := by
  exact kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleCoeff
    G embedding hdeg
      (kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning
        G embedding hdeg hturning)


theorem kacWard_straightLine_trivalent_of_cycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (hturning : KWStraightLineCycleTurning G embedding)
    (weight : Sym2 V → ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  exact kacWard_straightLine_trivalent_of_cycleCoeff G embedding hdeg
    (kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning
      G embedding hdeg hturning)
    weight q hq hentry hcard


end StatMech.FrontierA
