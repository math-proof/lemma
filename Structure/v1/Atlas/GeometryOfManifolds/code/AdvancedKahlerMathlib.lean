/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahlerMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option autoImplicit false


/-- A compact (nonempty) Kähler manifold of complex dimension $n$, abstractly bundled with
its topology and the assumption of compactness. -/
structure CompactKahlerManifold (n : ℕ) where
  carrier : Type*
  topInst : TopologicalSpace carrier
  isCompact : @CompactSpace carrier topInst
  isNonempty : Nonempty carrier


/-- Hodge / bidegree decomposition data for a compact Kähler manifold:
$$b_k = \sum_{p+q=k} h^{p,q}, \qquad h^{p,q} = h^{q,p}, \qquad h^{p,q} = h^{n-q,\,n-p}.$$
The first identity is the Hodge decomposition, the second is complex conjugation
symmetry, and the third is Serre / Hodge $\star$ duality. -/
structure BidegreeDecomposition (n : ℕ) (_M : CompactKahlerManifold n) where
  hodge : ℕ → ℕ → ℕ
  betti : ℕ → ℕ
  hodge_decomposition : ∀ (k : ℕ),
    betti k = (Finset.range (k + 1)).sum (fun p => hodge p (k - p))
  conjugation_symmetry : ∀ p q, hodge p q = hodge q p
  star_symmetry : ∀ p q, hodge p q = hodge (n - q) (n - p)


