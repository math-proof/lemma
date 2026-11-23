/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
public import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
public import Instance.v1.Atlas.BooleanFunctions.code.UniqueGames.Part4

@[expose] public section

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
