/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/WrittenOnTheWallII_GraphConjecture314_conjecture314.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace WrittenOnTheWallII.GraphConjecture314

set_option linter.all false

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }
