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


public section

namespace UniqueGames

structure UniqueGame (V : Type*) (W : Type*) [DecidableEq V] [DecidableEq W] (k : ℕ) where
  edges : Finset (V × W)
  constraint : V → W → Equiv.Perm (Fin k)
  left_degree : ℕ
  right_degree : ℕ
  left_regular : ∀ v : V, (edges.filter (fun e => e.1 = v)).card = left_degree
  right_regular : ∀ w : W, (edges.filter (fun e => e.2 = w)).card = right_degree

structure Labeling (V : Type*) (W : Type*) (k : ℕ) where
  labelV : V → Fin k
  labelW : W → Fin k

end UniqueGames
