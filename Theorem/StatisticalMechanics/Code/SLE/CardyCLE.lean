/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
import Def.StatisticalMechanics.Code.SLE.CardyCLE
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma discConformalRadius_apply (r : ℝ) : discConformalRadius r = r := rfl


end StatMech.SLE
