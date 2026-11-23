/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part4

@[expose] public section

namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

def numVertices (w : HexWalk) : ℕ := w.turns.length + 1

end HexWalk
end StatMech.Universality
