/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part4
import Mathlib.Topology.Connected.TotallyDisconnected
open scoped BigOperators
open Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kw_continuousAt_angleToReal
    {θ : Real.Angle} (hθ : θ ≠ (Real.pi : Real.Angle)) :
    ContinuousAt Real.Angle.toReal θ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hcut : θ ≠ ((-Real.pi : ℝ) : Real.Angle) := by
    simpa [Real.Angle.coe_neg, Real.Angle.neg_coe_pi] using hθ
  have hchart := AddCircle.continuousAt_equivIoc
    (p := 2 * Real.pi) (a := -Real.pi) hcut
  exact continuous_subtype_val.continuousAt.comp hchart


theorem kw_continuousOn_principalHalfAnglePhase
    {X D : Type*} [TopologicalSpace X]
    (angle : X → D → Real.Angle) (s : Set X) (dart next : D)
    (hdart : ContinuousOn (fun x ↦ angle x dart) s)
    (hnext : ContinuousOn (fun x ↦ angle x next) s)
    (hnondegenerate : ∀ x ∈ s,
      angle x next - angle x dart ≠ (Real.pi : Real.Angle)) :
    ContinuousOn
      (fun x ↦ kwPrincipalHalfAnglePhase (angle x) dart next) s := by
  intro x hx
  have hdelta : ContinuousWithinAt
      (fun y ↦ angle y next - angle y dart) s x :=
    (hnext x hx).sub (hdart x hx)
  have hreal : ContinuousWithinAt
      (fun y ↦ (angle y next - angle y dart).toReal) s x :=
    (kw_continuousAt_angleToReal
      (hnondegenerate x hx)).comp_continuousWithinAt
        (f := fun y ↦ angle y next - angle y dart) hdelta
  have hcoe : ContinuousWithinAt
      (fun y ↦ ((angle y next - angle y dart).toReal : ℂ)) s x :=
    Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hreal
  have harg : ContinuousWithinAt
      (fun y ↦ ((angle y next - angle y dart).toReal : ℂ) *
        Complex.I / 2) s x :=
    (hcoe.mul continuousWithinAt_const).div_const 2
  exact Complex.continuous_exp.continuousAt.comp_continuousWithinAt harg


end StatMech.FrontierA
