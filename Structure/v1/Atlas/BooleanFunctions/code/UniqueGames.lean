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
