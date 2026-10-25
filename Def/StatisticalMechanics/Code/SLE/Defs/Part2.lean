/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

def closedUpperHalfPlane : Set ℂ := {z : ℂ | 0 ≤ z.im}

end StatMech.SLE
