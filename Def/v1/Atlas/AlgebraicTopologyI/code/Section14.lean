/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section14
open Topology


namespace CWComplex

variable {X : Type*} [TopologicalSpace X]

/-- A CW-complex is finite-dimensional (Definition 14.7) if there is some `n` beyond
which there are no cells, i.e., $\mathrm{Sk}_n X = X$ for some `n`. -/
def IsFiniteDimensional (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∃ n : ℕ, ∀ m : ℕ, n ≤ m → IsEmpty (cells X m)

/-- A CW-complex is of finite type (Definition 14.7) if each set of `n`-cells $A_n$
is finite. -/
def IsFiniteType (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  ∀ n : ℕ, Finite (cells X n)

/-- A CW-complex is finite (Definition 14.7) if it is both finite-dimensional and of
finite type. Equivalently, it has only finitely many cells in total. -/
def IsFinite (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  IsFiniteDimensional X ∧ IsFiniteType X

end CWComplex
