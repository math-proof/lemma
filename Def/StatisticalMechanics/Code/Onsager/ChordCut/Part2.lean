/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.ChordCut

@[expose] public section

namespace StatMech.Onsager.ChordCut

open scoped BigOperators


def isDir (d : Pt) : Prop :=
  d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

end StatMech.Onsager.ChordCut
