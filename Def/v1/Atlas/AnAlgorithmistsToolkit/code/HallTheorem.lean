/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hall
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders.Part2
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders

@[expose] public section

open Finset Function SimpleGraph


namespace HallTheorem

def BipartiteExpander {L R : Type*} [DecidableEq R] [Fintype L]
    (neighbors : L → Finset R) (α β : ℝ) : Prop :=
  ∀ (S : Finset L),
    (S.card : ℝ) ≤ α * (Fintype.card L : ℝ) →
    (β * S.card : ℝ) ≤ ((S.biUnion neighbors).card : ℝ)

end HallTheorem
