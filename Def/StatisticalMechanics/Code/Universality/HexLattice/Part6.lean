module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

noncomputable def endMid (w : HexWalk) : ℂ := (w.mids).getLast (by simp [length_mids, List.ne_nil_of_length_pos])


def turnCount (w : HexWalk) : ℤ := w.turns.sum

end HexWalk
end StatMech.Universality
