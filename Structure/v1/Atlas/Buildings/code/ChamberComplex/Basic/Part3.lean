/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part2
variable {V : Type*} [DecidableEq V]


/-- A chamber complex: every face is contained in some chamber, and any two chambers are
connected by a gallery. -/
structure ChamberComplex (V : Type*) [DecidableEq V] extends SimplicialComplex V where
  exists_maximal : ∀ s ∈ faces, ∃ C, toSimplicialComplex.IsMaximal C ∧ s ⊆ C
  gallery_connected : ∀ C D, toSimplicialComplex.IsMaximal C →
    toSimplicialComplex.IsMaximal D → ∃ g : Gallery toSimplicialComplex,
    g.chambers.head? = some C ∧ g.chambers.getLast? = some D

