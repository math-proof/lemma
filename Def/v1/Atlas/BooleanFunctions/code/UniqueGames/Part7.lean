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
import Instance.v1.Atlas.BooleanFunctions.code.UniqueGames.Part4


namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def LabelCover.numSatisfiedEdges {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l) : ℕ :=
  (game.edges.filter (fun p => game.edgeSatisfied labeling p.1 p.2)).card

noncomputable def LabelCover.fractionSatisfied {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) (labeling : LabelCover.Labeling V W k l) : ℝ :=
  (game.numSatisfiedEdges labeling : ℝ) / (game.edges.card : ℝ)

noncomputable def LabelCover.value {V : Type*} {W : Type*} {k l : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : LabelCover V W k l) : ℝ :=
  iSup (fun labeling : LabelCover.Labeling V W k l => game.fractionSatisfied labeling)

def LabelCover.IsUnique {V : Type*} {W : Type*} {k l : ℕ}
    (game : LabelCover V W k l) : Prop :=
  k = l ∧ ∀ v w, (⟨v, w⟩ : V × W) ∈ game.edges →
    Function.Bijective (game.constraint v w)

end UniqueGames
