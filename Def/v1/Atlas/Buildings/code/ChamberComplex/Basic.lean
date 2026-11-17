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
public import Structure.v1.Atlas.Buildings.code.ChamberComplex.Basic

@[expose] public section

variable {V : Type*} [DecidableEq V]


namespace SimplicialComplex

/-- `y` is a face of `x` in `K`: both are faces of $K$ and $y ⊆ x$. -/
def IsFace (K : SimplicialComplex V) (y x : Finset V) : Prop :=
  y ∈ K.faces ∧ x ∈ K.faces ∧ y ⊆ x

/-- `y` is a codimension-$1$ face ("facet") of `x` in `K`: $y$ is a face of $x$ with
$|x \setminus y| = 1$. -/
def IsFacet (K : SimplicialComplex V) (y x : Finset V) : Prop :=
  K.IsFace y x ∧ (x \ y).card = 1

/-- `x` is a maximal face ("chamber") of `K`: a face contained in no strictly larger face. -/
def IsMaximal (K : SimplicialComplex V) (x : Finset V) : Prop :=
  x ∈ K.faces ∧ ∀ y ∈ K.faces, x ⊆ y → x = y

/-- Two distinct chambers $C, D$ are adjacent if they share a common codim-$1$ facet $F$. -/
def Adjacent (K : SimplicialComplex V) (C D : Finset V) : Prop :=
  K.IsMaximal C ∧ K.IsMaximal D ∧ C ≠ D ∧ ∃ F, K.IsFacet F C ∧ K.IsFacet F D

end SimplicialComplex
