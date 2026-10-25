/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericShear.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardShearPhaseHomotopy


namespace StatMech.FrontierA

open scoped BigOperators

open Set

@[simp] theorem kwDoubleShearLinearEquiv_zero (tx ty : ℝ) (z : ℂ) :
    kwDoubleShearLinearEquiv tx ty 0 z = z := by
  apply Complex.ext <;>
    simp [kwDoubleShearLinearEquiv, kwShearXLinearEquiv,
      kwShearYLinearEquiv, kwShearX, kwShearY]

@[simp] theorem kwDoubleShearLinearEquiv_one (tx ty : ℝ) (z : ℂ) :
    kwDoubleShearLinearEquiv tx ty 1 z =
      kwShearY ty (kwShearX tx z) := by
  simp [kwDoubleShearLinearEquiv, kwShearXLinearEquiv,
    kwShearYLinearEquiv]

theorem continuous_kwDoubleShearLinearEquiv_apply (tx ty : ℝ) (z : ℂ) :
    Continuous (fun t : ℝ ↦ kwDoubleShearLinearEquiv tx ty t z) := by
  change Continuous (fun t : ℝ ↦
    kwShearY (t * ty) (kwShearX (t * tx) z))
  unfold kwShearX kwShearY
  fun_prop

theorem continuousOn_kwDoubleShear_edge_arg
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (tx ty : ℝ) (k : Fin n) :
    ContinuousOn (fun t : ℝ ↦
      (Complex.arg (kwDoubleShearLinearEquiv tx ty t
        (polygon.edgeVector k)) : Real.Angle)) (Icc 0 1) := by
  intro t _
  have hedge : ContinuousAt (fun s : ℝ ↦
      kwDoubleShearLinearEquiv tx ty s (polygon.edgeVector k)) t :=
    (continuous_kwDoubleShearLinearEquiv_apply tx ty
      (polygon.edgeVector k)).continuousAt
  have hedgeNe : kwDoubleShearLinearEquiv tx ty t
      (polygon.edgeVector k) ≠ 0 := by
    apply (kwDoubleShearLinearEquiv tx ty t).map_ne_zero_iff.mpr
    unfold KWFiniteSimplePolygon.edgeVector
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne
      (polygon.add_one_ne_self k))
  have hc := (Complex.continuousAt_arg_coe_angle hedgeNe).comp
    (f := fun s : ℝ ↦ kwDoubleShearLinearEquiv tx ty s
      (polygon.edgeVector k)) hedge
  simpa only [Function.comp_apply] using hc.continuousWithinAt


theorem KWFiniteSimplePolygon.phaseCycle_mapDoubleShear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (tx ty : ℝ) :
    kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle
        (polygon.mapLinearEquiv
          (kwDoubleShearLinearEquiv tx ty 1)).edgeList := by
  let angle : ℝ → Fin n → Real.Angle := fun t k ↦
    (Complex.arg (kwDoubleShearLinearEquiv tx ty t
      (polygon.edgeVector k)) : Real.Angle)
  have hcontinuous (k : Fin n) : ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t) k (k + 1))
      (Icc 0 1) := by
    apply kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1) k (k + 1)
    · exact continuousOn_kwDoubleShear_edge_arg polygon tx ty k
    · exact continuousOn_kwDoubleShear_edge_arg polygon tx ty (k + 1)
    · intro t _
      let transformed := polygon.mapLinearEquiv
        (kwDoubleShearLinearEquiv tx ty t)
      have hturn := transformed.consecutive_turn_ne_pi k
      simpa only [transformed, KWFiniteSimplePolygon.mapLinearEquiv_edgeVector,
        angle] using hturn
  have hinvariant := kwLoopPhaseProduct_principal_homotopy
    angle (fun k : Fin n ↦ k) hcontinuous
  rw [KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn,
    KWFiniteSimplePolygon.edgeList, kwVectorPhaseCycle_ofFn]
  simpa only [kwLoopPhaseProduct, kwPrincipalHalfAnglePhase,
    kwVectorTurnPhase, kwAngleTurnPhase, angle,
    kwDoubleShearLinearEquiv_zero,
    KWFiniteSimplePolygon.mapLinearEquiv_edgeVector] using hinvariant

end StatMech.FrontierA
