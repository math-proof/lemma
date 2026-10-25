/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def triangularTorusDirectionAngleReal : Fin 6 -> Real :=
  ![Real.pi, 0, -Real.pi / 2, Real.pi / 2,
    -3 * Real.pi / 4, Real.pi / 4]

noncomputable def triangularTorusDirectionAngle (a : Fin 6) : Real.Angle :=
  (triangularTorusDirectionAngleReal a : Real.Angle)

end StatMech.FrontierA
