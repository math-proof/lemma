module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part3
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwPrincipalHalfAngleBranch
    {D : Type*} (angle : D → Real.Angle) : D → D → ℂ :=
  fun dart next ↦ kwPrincipalHalfAngleRoot angle dart *
    kwPrincipalHalfAnglePhase angle dart next *
      (kwPrincipalHalfAngleRoot angle next)⁻¹


end StatMech.FrontierA
