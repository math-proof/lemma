/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CorBilinearHermitianForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Fin.Eq_Neg.of.IsAlt
set_option maxHeartbeats 4000000


namespace Formalization.GeometricAlgebra

open Garrett

variable {k : Type*} [Field k] [Invertible (2 : k)]


/-- A bilinear form `B` is anisotropic on a subspace `W` iff every isotropic vector
in `W` (one with `B x x = 0`) is zero. -/
def BilinForm.IsAnisotropicOn {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (W : Submodule k V) : Prop :=
  ∀ x ∈ W, B x x = 0 → x = 0

/-- A subspace `H` is a hyperbolic subspace for `B` iff it is spanned by `n` mutually
orthogonal hyperbolic pairs `(vs i, ws i)` (i.e. `B (vs i) (vs i) = B (ws i) (ws i) = 0`,
`B (vs i) (ws i) = 1`, and the cross-pairings between distinct pairs vanish). -/
def BilinForm.IsHyperbolicSubspace' {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (H : Submodule k V) : Prop :=
  ∃ (n : ℕ) (vs ws : Fin n → V),
    (∀ i, vs i ∈ H) ∧ (∀ i, ws i ∈ H) ∧
    (∀ i, B (vs i) (vs i) = 0) ∧
    (∀ i, B (ws i) (ws i) = 0) ∧
    (∀ i, B (vs i) (ws i) = 1) ∧
    (∀ i j, i ≠ j → B (vs i) (vs j) = 0) ∧
    (∀ i j, i ≠ j → B (ws i) (ws j) = 0) ∧
    (∀ i j, i ≠ j → B (vs i) (ws j) = 0) ∧
    H = Submodule.span k (Set.range vs ∪ Set.range ws)

end Formalization.GeometricAlgebra
