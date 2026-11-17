/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
public import Def.StatisticalMechanics.Code.SLE.CardyCLE
open scoped UpperHalfPlane NNReal
open Complex Filter Topology

public section

namespace StatMech.SLE

@[simp] lemma discConformalRadius_apply (r : ℝ) : discConformalRadius r = r := rfl


end StatMech.SLE
