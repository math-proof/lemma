/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part9
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def ghost : Option V := none


def withGhost : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some x, some y => G.Adj x y
    | some _, none => True
    | none, some _ => True
    | none, none => False
  symm := by
    constructor
    rintro (_ | x) (_ | y) h
    · exact h
    · exact h
    · exact h
    · exact G.symm.symm x y h
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact G.loopless.irrefl x h⟩

end Sharpness
end StatMech
