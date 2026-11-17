/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.StatisticalMechanics.Code.Onsager.ChordCut.Part2

@[expose] public section

namespace StatMech.Onsager.ChordCut

open scoped BigOperators


instance (d : Pt) : Decidable (isDir d) := by unfold isDir; infer_instance


end StatMech.Onsager.ChordCut
