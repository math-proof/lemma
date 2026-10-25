/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders.Part2
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Expanders
open Finset Function SimpleGraph


namespace HallTheorem

def BipartiteExpander {L R : Type*} [DecidableEq R] [Fintype L]
    (neighbors : L → Finset R) (α β : ℝ) : Prop :=
  ∀ (S : Finset L),
    (S.card : ℝ) ≤ α * (Fintype.card L : ℝ) →
    (β * S.card : ℝ) ≤ ((S.biUnion neighbors).card : ℝ)

end HallTheorem
