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
public import Def.v1.Atlas.BooleanFunctions.code.UniqueGames

@[expose] public section

namespace UniqueGames

instance {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) (labeling : Labeling V W k) (v : V) (w : W) :
    Decidable (edgeSatisfied game labeling v w) :=
  inferInstanceAs (Decidable (_ = _))

end UniqueGames
