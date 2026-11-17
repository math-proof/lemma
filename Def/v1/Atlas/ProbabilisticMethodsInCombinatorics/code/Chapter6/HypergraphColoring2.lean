/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/HypergraphColoring2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Finset.Powerset

@[expose] public section

set_option maxHeartbeats 400000

open Set Topology


namespace HypergraphColoring

variable {V : Type*}

/-- Set of 2-colorings of `V` that properly color every hyperedge `e ∈ edges` contained in the
finite vertex set `X` (no edge entirely monochromatic). Used in the compactness step of
Theorem 6.2.4. -/
def goodColorings624 (edges : Set (Finset V)) (X : Finset V) : Set (V → Bool) :=
  {c | ∀ e ∈ edges, (↑e : Set V) ⊆ ↑X →
    ¬(∀ v ∈ e, c v = true) ∧ ¬(∀ v ∈ e, c v = false)}

end HypergraphColoring
