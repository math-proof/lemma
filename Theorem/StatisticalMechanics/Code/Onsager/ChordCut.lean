/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ChordCut


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


theorem cross_antisymm (a b : Pt) : cross a b = - cross b a := by
  simp only [cross]; ring


end StatMech.Onsager.ChordCut
