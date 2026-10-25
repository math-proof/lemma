/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearGraphCancellation
import Theorem.StatisticalMechanics.Code.Onsager.StateWeightedDeletion
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

theorem kwGraphTransition_scaleEdge_entry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ)
    (selected dart next : G.Dart) (t : ℂ) :
    kwGraphTransition G
        (kwScaleGraphEdgeWeight weight selected.edge t) phase dart next =
      (if dart.edge = selected.edge then t else 1) *
        kwGraphTransition G weight phase dart next := by
  classical
  unfold kwGraphTransition kwScaleGraphEdgeWeight
  by_cases hedge : dart.edge = selected.edge
  · simp [hedge]
    split <;> ring
  · simp [hedge]


theorem kw_loopWeight_scaleGraphEdge_eq_scaleColumns
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ)
    (selected : G.Dart) (t : ℂ) (loop : Fin n -> G.Dart) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t) phase) loop =
      StatMech.Onsager.ons_loopWeight
        (StatMech.Onsager.ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight phase)) loop := by
  unfold StatMech.Onsager.ons_loopWeight
  rw [Finset.prod_congr rfl (fun k _ =>
    kwGraphTransition_scaleEdge_entry
      G weight phase selected (loop k) (loop (k + 1)) t),
    Finset.prod_mul_distrib]
  have hreindex :
      (∏ k, if (loop (k + 1)).edge = selected.edge then t else 1) =
        ∏ k, if (loop k).edge = selected.edge then t else 1 :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k => if (loop k).edge = selected.edge then t else 1)
  rw [← hreindex, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [StatMech.Onsager.ons_scaleColumns]
  by_cases hmem : loop (k + 1) ∈
      ({selected, selected.symm} : Finset G.Dart)
  · have hedge : (loop (k + 1)).edge = selected.edge :=
      (kw_dart_mem_reversePair_iff_edge_eq selected _).mp hmem
    simp [hmem, hedge]
  · have hedge : (loop (k + 1)).edge ≠ selected.edge := fun hedge =>
      hmem ((kw_dart_mem_reversePair_iff_edge_eq selected _).mpr hedge)
    simp [hmem, hedge]


theorem kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ)
    (selected : G.Dart) (t : ℂ) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t) phase) =
      StatMech.Onsager.ons_detWalkRoot
        (StatMech.Onsager.ons_scaleColumns
          ({selected, selected.symm} : Finset G.Dart) t
          (kwGraphTransition G weight phase)) := by
  apply StatMech.Onsager.ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact kw_loopWeight_scaleGraphEdge_eq_scaleColumns
    G weight phase selected t loop


theorem kw_rectilinearGraph_detWalkRoot_scaleEdge_affine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (t : ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖StatMech.Onsager.ons_scaleColumns
        ({selected, selected.symm} : Finset G.Dart) t
        (kwGraphTransition G weight
          (fun d e => StatMech.Onsager.ons_turnW omega
            (direction e) (direction d))) dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
    StatMech.Onsager.ons_detWalkRoot
        (kwGraphTransition G
          (kwScaleGraphEdgeWeight weight selected.edge t)
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) =
      StatMech.Onsager.ons_detWalkRoot
          (StatMech.Onsager.ons_maskMatrix
            ({selected, selected.symm} : Finset G.Dart)
            (kwGraphTransition G weight
              (fun dart next => StatMech.Onsager.ons_turnW omega
                (direction next) (direction dart)))) *
        (1 - t * ∑' path, StatMech.Onsager.ons_firstReturnWeight
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))
          selected selected.symm path) := by
  rw [kw_detWalkRoot_scaleGraphEdge_eq_scaleColumns]
  exact kw_rectilinearGraph_detWalkRoot_scaleColumns_affine
    G weight direction hdirection omega homega homega_sq
    selected t q hq hentry hsmall hcard

end StatMech.FrontierA
