/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section14.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
open Topology


/-- A CW-complex structure on a topological space `X`, identified with a CW-complex
structure on the universe set `Set.univ : Set X` from mathlib's `Topology.CWComplex`. -/
abbrev CWComplex (X : Type*) [TopologicalSpace X] : Type _ :=
  Topology.CWComplex (Set.univ : Set X)

namespace CWComplex

variable {X : Type*} [TopologicalSpace X]

/-- The indexing type of `n`-cells in a CW-complex `X`. These are the cells $A_n$
appearing in the attaching pushout for $\mathrm{Sk}_n X$. -/
abbrev cells (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) : Type _ :=
  Topology.CWComplex.cell (Set.univ : Set X) n

/-- The `n`-skeleton $\mathrm{Sk}_n X$ of a CW-complex, defined for `n : ℕ∞`. This is
the subspace obtained by attaching all cells of dimension at most `n`, as in
Definition 14.5. -/
noncomputable abbrev skeleton (X : Type*) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ∞) :=
  Topology.CWComplex.skeleton (Set.univ : Set X) n

end CWComplex
