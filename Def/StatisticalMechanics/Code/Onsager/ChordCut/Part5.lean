/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.ChordCut.Part3

@[expose] public section

namespace StatMech.Onsager.ChordCut

open scoped BigOperators


def chordInterior (w : Pt) (k : ℕ) : List Pt :=
  (List.range' 1 (k - 1)).map (rayX w)


end StatMech.Onsager.ChordCut
