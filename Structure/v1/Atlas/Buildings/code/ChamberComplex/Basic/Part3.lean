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
public import Def.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part2
public section

variable {V : Type*} [DecidableEq V]


/-- A chamber complex: every face is contained in some chamber, and any two chambers are
connected by a gallery. -/
structure ChamberComplex (V : Type*) [DecidableEq V] extends SimplicialComplex V where
  exists_maximal : ∀ s ∈ faces, ∃ C, toSimplicialComplex.IsMaximal C ∧ s ⊆ C
  gallery_connected : ∀ C D, toSimplicialComplex.IsMaximal C →
    toSimplicialComplex.IsMaximal D → ∃ g : Gallery toSimplicialComplex,
    g.chambers.head? = some C ∧ g.chambers.getLast? = some D

