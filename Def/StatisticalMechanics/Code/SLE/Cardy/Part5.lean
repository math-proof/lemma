/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part4
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

noncomputable def sleDimension (κ : ℝ) : ℝ := 1 + κ / 8

end StatMech.SLE
