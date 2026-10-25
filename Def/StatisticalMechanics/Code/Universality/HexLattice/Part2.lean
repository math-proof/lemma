/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Universality.HexLattice


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

def headingsAux (h : ℤ) : List ℤ → List ℤ
  | [] => [h]
  | t :: ts => h :: headingsAux (h + t) ts


def headings (w : HexWalk) : List ℤ := headingsAux w.h0 w.turns

end HexWalk
end StatMech.Universality
