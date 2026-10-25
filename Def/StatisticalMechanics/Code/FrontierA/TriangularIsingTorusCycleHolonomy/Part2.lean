/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


def triangularIntPoint (p : Int × Int) : Complex :=
  (p.1 : Real) + (p.2 : Real) * Complex.I

end StatMech.FrontierA
