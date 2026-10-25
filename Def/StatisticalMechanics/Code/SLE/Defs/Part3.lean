/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part2
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

def realLine : Set ℂ := {z : ℂ | z.im = 0}

end StatMech.SLE
