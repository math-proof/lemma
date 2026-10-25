/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwGraphTransition_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (gauge : G.Dart → ℂ) :
    kwGraphTransition G weight (kwPhaseGauge gauge phase) =
      kwGaugeConjugate gauge (kwGraphTransition G weight phase) := by
  ext dart next
  by_cases hstep : dart.snd = next.fst ∧ dart.edge ≠ next.edge
  · simp [kwGraphTransition, kwPhaseGauge, kwGaugeConjugate, hstep]
    ring
  · simp [kwGraphTransition, kwGaugeConjugate, hstep]


theorem kwGraphLoopScalar_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (gauge : G.Dart → ℂ)
    (hgauge : ∀ dart, gauge dart ≠ 0)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G (kwPhaseGauge gauge phase) loop =
      kwGraphLoopScalar G phase loop := by
  change ons_loopWeight
      (kwGraphTransition G (fun _ ↦ 1) (kwPhaseGauge gauge phase)) loop =
    ons_loopWeight (kwGraphTransition G (fun _ ↦ 1) phase) loop
  rw [kwGraphTransition_phaseGauge]
  exact kw_loopWeight_gaugeConjugate gauge _ hgauge loop


theorem kwGraphFormalLog_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (gauge : G.Dart → ℂ)
    (hgauge : ∀ dart, gauge dart ≠ 0) :
    kwGraphFormalLog G (kwPhaseGauge gauge phase) =
      kwGraphFormalLog G phase := by
  ext m
  change kwGraphFormalLogCoeff G (kwPhaseGauge gauge phase) m =
    kwGraphFormalLogCoeff G phase m
  unfold kwGraphFormalLogCoeff
  apply congrArg (fun z : ℂ ↦ -z / 2)
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  apply Finset.sum_congr rfl
  intro loop _
  by_cases heq : kwGraphLoopExponent G loop = m
  · simp only [if_pos heq]
    exact kwGraphLoopScalar_phaseGauge G phase gauge hgauge loop
  · simp [heq]


theorem kwGraphFormalRoot_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (gauge : G.Dart → ℂ)
    (hgauge : ∀ dart, gauge dart ≠ 0) :
    kwGraphFormalRoot G (kwPhaseGauge gauge phase) =
      kwGraphFormalRoot G phase := by
  unfold kwGraphFormalRoot
  rw [kwGraphFormalLog_phaseGauge G phase gauge hgauge]


theorem kw_detWalkRoot_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0) :
    ons_detWalkRoot
        (kwGraphTransition G weight (kwPhaseGauge gauge phase)) =
      ons_detWalkRoot (kwGraphTransition G weight phase) := by
  rw [kwGraphTransition_phaseGauge]
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact kw_loopWeight_gaugeConjugate gauge _ hgauge loop


theorem kw_det_one_sub_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0) :
    (1 - kwGraphTransition G weight (kwPhaseGauge gauge phase)).det =
      (1 - kwGraphTransition G weight phase).det := by
  rw [kwGraphTransition_phaseGauge]
  exact kw_det_one_sub_gaugeConjugate gauge _ hgauge


end StatMech.FrontierA
