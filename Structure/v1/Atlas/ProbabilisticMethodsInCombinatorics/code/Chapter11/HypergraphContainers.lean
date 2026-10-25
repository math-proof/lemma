/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter11/HypergraphContainers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
set_option maxHeartbeats 800000

open Finset Real


namespace HypergraphContainers

/-- A 3-uniform hypergraph on a finite vertex type $V$: a finite family of 3-element
subsets of $V$. -/
structure ThreeUniformHypergraph (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Finset V)
  edges_card : ∀ e ∈ edges, e.card = 3

end HypergraphContainers
