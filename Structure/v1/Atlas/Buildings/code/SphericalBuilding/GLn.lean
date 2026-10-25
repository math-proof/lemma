/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.RelClasses
import Mathlib.Data.Matrix.Basic
import Abbrev.v1.Atlas.Buildings.code.SphericalBuilding.GLn


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Abstract data of a flag-like simplicial complex: a vertex type, a simplex type, and a
function assigning to each simplex its finite set of vertices. -/
structure FlagData where
  vertex : Type*
  simplex : Type*
  verticesOf : simplex → Finset vertex

/-- A simplex of the $\mathrm{GL}_n(k)$-building: a non-empty, strictly increasing chain of
proper non-zero subspaces $0 \subsetneq V_1 \subsetneq \cdots \subsetneq V_r \subsetneq k^n$. -/
structure SubspaceFlag where
  chain : List (Submodule k (Vec k n))
  chain_nonempty : chain ≠ []
  chain_strictly_increasing : chain.IsChain (· < ·)
  chain_proper : ∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤

end GLnBuilding
