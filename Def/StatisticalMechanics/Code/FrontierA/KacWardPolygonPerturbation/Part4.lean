/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part3


namespace StatMech.FrontierA

open scoped Convex

open Set

def kwRatVertex {n : ℕ} (q : Fin n → ℚ × ℚ) : Fin n → ℂ :=
  fun i ↦ kwRatComplex (q i)

end StatMech.FrontierA
