/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3OpenImmersion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Irreducible

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X]

/-- A subset `s` of a topological space is an *irreducible component* if it is closed, irreducible,
and maximal among closed irreducible subsets containing it. -/
def IsIrreducibleComponent (s : Set X) : Prop :=
  IsClosed s ∧ IsIrreducible s ∧ ∀ t : Set X, IsClosed t → IsIrreducible t → s ⊆ t → t = s
