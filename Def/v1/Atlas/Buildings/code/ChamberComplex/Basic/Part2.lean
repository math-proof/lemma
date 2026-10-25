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
import Structure.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part2
variable {V : Type*} [DecidableEq V]


/-- The combinatorial length of a gallery: number of edges = (number of chambers) $- 1$. -/
def Gallery.length {K : SimplicialComplex V} (g : Gallery K) : ℕ :=
  g.chambers.length - 1

/-- The gallery `g` "connects" $C$ to $D$ if its first chamber is $C$ and its last chamber is $D$. -/
def Gallery.Connects {K : SimplicialComplex V} (g : Gallery K) (C D : Finset V) : Prop :=
  g.chambers.head? = some C ∧ g.chambers.getLast? = some D

