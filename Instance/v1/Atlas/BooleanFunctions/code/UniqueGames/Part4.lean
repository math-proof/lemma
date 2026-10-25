/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part6


namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

instance {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l)
    (v : V) (w : W) :
    Decidable (game.edgeSatisfied labeling v w) :=
  inferInstanceAs (Decidable (_ = _))

end UniqueGames
