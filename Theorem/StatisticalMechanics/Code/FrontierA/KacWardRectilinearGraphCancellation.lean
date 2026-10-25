/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearGraphCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFixedMonomialCancellation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearGraphCancellation
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

theorem kwGraphNonbacktrackingFactor_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (dart next : G.Dart) :
    kwGraphNonbacktrackingFactor G next.symm dart.symm =
      kwGraphNonbacktrackingFactor G dart next := by
  simp [kwGraphNonbacktrackingFactor, SimpleGraph.DartAdj, eq_comm]


theorem kwGraphTransition_turnW_eq_stateWeighted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (omega : ℂ) :
    kwGraphTransition G weight
        (fun dart next => StatMech.Onsager.ons_turnW omega
          (direction next) (direction dart)) =
      StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix
        direction omega (fun dart => weight dart.edge) (fun _ => 1)
        (kwGraphNonbacktrackingFactor G) := by
  classical
  ext dart next
  simp only [kwGraphTransition,
    StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix,
    kwGraphNonbacktrackingFactor, SimpleGraph.DartAdj, one_mul]
  by_cases hadj : dart.snd = next.fst
  · by_cases hedge : dart.edge = next.edge
    · simp [hadj, hedge]
    · simp [hadj, hedge]
  · simp [hadj]


theorem kw_rectilinearGraph_fixedOrbitExponent_cancel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (exponent : Sym2 G.Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight
          (fun dart next => StatMech.Onsager.ons_turnW omega
            (direction next) (direction dart))) loop) = 0 := by
  rw [kwGraphTransition_turnW_eq_stateWeighted]
  exact kw_fixedOrbitExponent_stateWeightedReversibleTurnMatrix_cancel
    SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
    direction hdirection omega homega homega_sq
    (fun dart => weight dart.edge) (fun _ => 1)
    (by intro dart; simp)
    (kwGraphNonbacktrackingFactor G)
    (kwGraphNonbacktrackingFactor_reverse G)
    selected (SimpleGraph.Dart.symm_ne selected) exponent


theorem kw_rectilinearGraph_fixedOrbitExponent_gauge_cancel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V -> ℂ) (direction : G.Dart -> Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart -> ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (selected : G.Dart) (exponent : Sym2 G.Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGaugeConjugate gauge
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))) loop) = 0 := by
  calc
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGaugeConjugate gauge
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart)))) loop) =
      ∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
        StatMech.Onsager.ons_loopWeight
          (kwGraphTransition G weight
            (fun dart next => StatMech.Onsager.ons_turnW omega
              (direction next) (direction dart))) loop := by
      apply Finset.sum_congr rfl
      intro loop _
      exact kw_loopWeight_gaugeConjugate gauge _ hgauge loop
    _ = 0 := kw_rectilinearGraph_fixedOrbitExponent_cancel
      G weight direction hdirection omega homega homega_sq selected exponent

end StatMech.FrontierA
