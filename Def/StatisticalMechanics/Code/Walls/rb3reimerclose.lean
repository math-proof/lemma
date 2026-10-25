/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
open Finset
open scoped BigOperators NNReal


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false


def rb3_toB {n : ℕ} (S : Finset (Fin n)) : rbt_Q n := fun i => decide (i ∈ S)


noncomputable def rb3_ofB {n : ℕ} (x : rbt_Q n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

end StatMech.Walls.Reimer
