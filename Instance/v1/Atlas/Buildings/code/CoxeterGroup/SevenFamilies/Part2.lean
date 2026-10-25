/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies.Part2


/-- The affine-$D$ adjacency predicate is decidable. -/
instance (n i j : ℕ) : Decidable (affinDCond n i j) := by unfold affinDCond; infer_instance

