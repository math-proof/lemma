/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/AnisotropicDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000

namespace Garrett

variable {F : Type*} [Field F]


/-- A bilinear form `B` is anisotropic when every isotropic vector (one with
`B x x = 0`) is zero. -/
def BilinForm.IsAnisotropic {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) : Prop :=
  ∀ x : V, B x x = 0 → x = 0

/-- A subspace `H` is hyperbolic for `B` iff it is spanned by `n` mutually orthogonal
hyperbolic pairs `(vs i, ws i)` with `B (vs i) (ws i) = 1` and all self-pairings and
cross-pairings between distinct pairs vanishing. -/
def BilinForm.IsHyperbolicSubspace {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (H : Submodule F V) : Prop :=
  ∃ (n : ℕ) (vs ws : Fin n → V),
    (∀ i, vs i ∈ H) ∧ (∀ i, ws i ∈ H) ∧
    (∀ i, B (vs i) (vs i) = 0) ∧
    (∀ i, B (ws i) (ws i) = 0) ∧
    (∀ i, B (vs i) (ws i) = 1) ∧
    (∀ i j, i ≠ j → B (vs i) (vs j) = 0) ∧
    (∀ i j, i ≠ j → B (ws i) (ws j) = 0) ∧
    (∀ i j, i ≠ j → B (vs i) (ws j) = 0) ∧
    H = Submodule.span F (Set.range vs ∪ Set.range ws)
