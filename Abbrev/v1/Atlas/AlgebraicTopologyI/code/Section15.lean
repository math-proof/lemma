/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval
open Topology


/-- **Definition 15.1.** A subcomplex of a CW-complex $X$ is a closed subspace
$Y \subseteq X$ that inherits a CW-structure from $X$: for each $n$ there is a
subset $B_n$ of the $n$-cells $A_n$ such that $Y_n = Y \cap X_n$ is given a
CW-structure by the characteristic maps $\{g_\beta : \beta \in B_n\}$.

In this formalization a `CWSubcomplex X` is unfolded to Mathlib's
`Topology.CWComplex.Subcomplex (Set.univ : Set X)`. -/
abbrev CWSubcomplex (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] : Type _ :=
  Topology.CWComplex.Subcomplex (Set.univ : Set X)

namespace CWSubcomplex

variable {X : Type*} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

/-- The indexing set of $n$-cells of the subcomplex `E`, viewed as a subset of
the indexing set of $n$-cells of the ambient CW-complex `X`. -/
abbrev cells (E : CWSubcomplex X) (n : ℕ) : Set (CWComplex.cells X n) :=
  E.I n

end CWSubcomplex
