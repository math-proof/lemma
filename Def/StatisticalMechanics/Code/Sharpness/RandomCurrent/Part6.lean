/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def backbone (n : Current V) (x y : V)
    [LinearOrder (IsBackbonePath G n x y)]
    (h : Nonempty (IsBackbonePath G n x y)) : IsBackbonePath G n x y :=
  (Finset.univ : Finset (IsBackbonePath G n x y)).min'
    (Finset.univ_nonempty_iff.mpr h)


end Sharpness
end StatMech
