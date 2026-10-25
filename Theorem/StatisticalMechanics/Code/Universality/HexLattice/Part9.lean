/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part9


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp] theorem ofTurns_turns (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).turns = ts := rfl

@[simp] theorem ofTurns_startMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).startMid = a := rfl

@[simp] theorem ofTurns_h0 (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).h0 = h0 := rfl

end HexWalk
end StatMech.Universality
