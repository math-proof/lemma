/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.NonnegDependence
@[expose] public section

open Finset Function


namespace NonnegDependence

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- Decidability of `extendsMatching`, by reducing to a finite conjunction over the edges of `F`. -/
instance decidableExtendsMatching (f : X ↪ Y) (F : Matching X Y) :
    Decidable (extendsMatching f F) :=
  inferInstanceAs (Decidable (∀ e ∈ F.edges, f e.1 = e.2))

end NonnegDependence
