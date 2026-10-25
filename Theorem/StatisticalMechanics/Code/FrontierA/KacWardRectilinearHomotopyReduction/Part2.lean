/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction


namespace StatMech.FrontierA

open scoped BigOperators

open Set

open StatMech.Onsager.BaseCase

theorem KWRectilinearPhaseHomotopy.angle_continuous
    {n m : ℕ} [NeZero n] [NeZero m]
    {source : KWFiniteSimplePolygon n}
    (h : KWRectilinearPhaseHomotopy source) (k : Fin m) :
    ContinuousOn
      (fun t ↦ (Complex.arg ((h.polygon t).edgeVector k) : Real.Angle))
      (Icc 0 1) := by
  intro t ht
  have hedge : ContinuousWithinAt
      (fun s ↦ (h.polygon s).edgeVector k) (Icc 0 1) t := by
    unfold KWFiniteSimplePolygon.edgeVector
    exact (h.vertex_continuous (k + 1) t ht).sub
      (h.vertex_continuous k t ht)
  have hne : (h.polygon t).edgeVector k ≠ 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [sub_ne_zero]
    exact (h.polygon t).vertex_injective.ne
      ((h.polygon t).add_one_ne_self k)
  simpa only [Function.comp_apply] using
    (Complex.continuousAt_arg_coe_angle hne).comp_continuousWithinAt
      (f := fun s ↦ (h.polygon s).edgeVector k) hedge


theorem KWRectilinearPhaseHomotopy.phaseProduct_zero_eq_one
    {n m : ℕ} [NeZero n] [NeZero m]
    {source : KWFiniteSimplePolygon n}
    (h : KWRectilinearPhaseHomotopy source) :
    (∏ k : Fin m, kwVectorTurnPhase
        ((h.polygon 0).edgeVector k) ((h.polygon 0).edgeVector (k + 1))) =
      ∏ k : Fin m, kwVectorTurnPhase
        ((h.polygon 1).edgeVector k) ((h.polygon 1).edgeVector (k + 1)) := by
  let angle : ℝ → Fin m → Real.Angle := fun t k ↦
    (Complex.arg ((h.polygon t).edgeVector k) : Real.Angle)
  have hcontinuous (k : Fin m) : ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t) k (k + 1))
      (Icc 0 1) := by
    apply kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1) k (k + 1)
    · exact h.angle_continuous k
    · exact h.angle_continuous (k + 1)
    · intro t ht
      exact h.turn_ne_pi t ht k
  have hinvariant := kwLoopPhaseProduct_principal_homotopy
    angle (fun k : Fin m ↦ k) hcontinuous
  simpa only [kwLoopPhaseProduct, kwPrincipalHalfAnglePhase,
    kwVectorTurnPhase, angle] using hinvariant


theorem KWRectilinearPhaseHomotopy.source_phaseCycle_eq_neg_one
    {n m : ℕ} [NeZero n] [NeZero m]
    {source : KWFiniteSimplePolygon n}
    (h : @KWRectilinearPhaseHomotopy n m _ _ source) :
    kwVectorPhaseCycle source.edgeList = -1 := by
  rw [h.source_phase, h.phaseProduct_zero_eq_one]
  have htarget :
      (∏ k : Fin m, kwVectorTurnPhase
        ((h.polygon 1).edgeVector k) ((h.polygon 1).edgeVector (k + 1))) =
      ∏ k : Fin m, kwVectorTurnPhase
        (kwRectilinearVector (h.direction k))
        (kwRectilinearVector (h.direction (k + 1))) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [h.target_edge k, h.target_edge (k + 1)]
    exact kwVectorTurnPhase_pos_scales
      (h.target_scale k) (h.target_scale (k + 1))
      (h.target_scale_pos k) (h.target_scale_pos (k + 1))
      (kwRectilinearVector (h.direction k))
      (kwRectilinearVector (h.direction (k + 1)))
      (kwRectilinearVector_ne_zero _) (kwRectilinearVector_ne_zero _)
  rw [htarget]
  exact kwRectilinearVector_phaseProduct_eq_neg_one
    h.direction h.direction_closed h.direction_simple
    h.direction_three_le h.direction_nonbacktracking


theorem kwFiniteSimplePolygonPhaseSign_of_rectilinearizable
    (hrect : KWFiniteSimplePolygonRectilinearizable) :
    KWFiniteSimplePolygonPhaseSign := by
  intro n inst source
  obtain ⟨m, instm, h⟩ := hrect source
  letI : NeZero m := instm
  exact h.some.source_phaseCycle_eq_neg_one

end StatMech.FrontierA
