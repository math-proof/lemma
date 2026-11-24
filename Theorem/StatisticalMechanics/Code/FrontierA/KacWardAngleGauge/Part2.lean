module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
public import Def.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part2
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


theorem kwRealHalfAngleRoot_ne_zero
    {D : Type*} (angle : D → ℝ) (dart : D) :
    kwRealHalfAngleRoot angle dart ≠ 0 :=
  Complex.exp_ne_zero _


end StatMech.FrontierA
