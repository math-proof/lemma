/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public section

variable {V : Type*} [DecidableEq V]


/-- An abstract simplicial complex on a vertex set $V$: a downward-closed family of
nonempty finite subsets ("faces") of $V$. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] where
  faces : Set (Finset V)
  nonempty_of_mem : ∀ s ∈ faces, s.Nonempty
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces

