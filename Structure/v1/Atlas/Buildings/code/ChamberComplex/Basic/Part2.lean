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
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Basic
public section

variable {V : Type*} [DecidableEq V]


/-- A gallery in `K`: a nonempty list of chambers in which consecutive entries are adjacent. -/
structure Gallery (K : SimplicialComplex V) where
  chambers : List (Finset V)
  length_pos : chambers.length > 0
  all_maximal : ∀ C ∈ chambers, K.IsMaximal C
  adjacent_consecutive : List.IsChain K.Adjacent chambers

