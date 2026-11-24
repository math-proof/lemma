module
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerCombinatorial
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerCombinatorial
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/TriangleIntersecting.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace TriangleIntersecting

/-- A family $F$ of graphs on a common vertex set is triangle-intersecting if every pair of
graphs in $F$ shares at least one triangle, i.e. $G_1 \cap G_2$ contains a 3-clique. -/
def IsTriangleIntersecting {n : ℕ} (F : Finset (SimpleGraph (Fin n))) : Prop :=
  ∀ G₁ ∈ F, ∀ G₂ ∈ F, ¬ (G₁ ⊓ G₂).CliqueFree 3

end TriangleIntersecting
