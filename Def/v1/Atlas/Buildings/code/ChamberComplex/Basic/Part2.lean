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
public import Structure.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part2

@[expose] public section

variable {V : Type*} [DecidableEq V]


/-- The combinatorial length of a gallery: number of edges = (number of chambers) $- 1$. -/
def Gallery.length {K : SimplicialComplex V} (g : Gallery K) : ℕ :=
  g.chambers.length - 1

/-- The gallery `g` "connects" $C$ to $D$ if its first chamber is $C$ and its last chamber is $D$. -/
def Gallery.Connects {K : SimplicialComplex V} (g : Gallery K) (C D : Finset V) : Prop :=
  g.chambers.head? = some C ∧ g.chambers.getLast? = some D

