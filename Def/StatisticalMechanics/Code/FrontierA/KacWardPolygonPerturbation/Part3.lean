/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part2


namespace StatMech.FrontierA

open scoped Convex

open Set

def kwRatComplex (q : ℚ × ℚ) : ℂ :=
  (q.1 : ℝ) + (q.2 : ℝ) * Complex.I

end StatMech.FrontierA
