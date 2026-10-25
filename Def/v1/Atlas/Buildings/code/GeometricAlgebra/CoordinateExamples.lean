/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CoordinateExamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Block
open Matrix


namespace CoordinateExamples

/-- The standard symplectic form matrix on `kⁿ ⊕ kⁿ`: the block matrix
`[[0, -1], [1, 0]]`. -/
noncomputable def symplecticFormMatrix (n : ℕ) (k : Type*) [Ring k] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The standard split-orthogonal (hyperbolic) form matrix on `kⁿ ⊕ kⁿ`: the
block matrix `[[0, 1], [1, 0]]`. -/
def splitOrthogonalFormMatrix (n : ℕ) (k : Type*) [Zero k] [One k] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  Matrix.fromBlocks 0 1 1 0

/-- The standard signature `(p, q)` orthogonal form matrix: the block-diagonal
matrix with `1`'s in the first `p` slots and `-1`'s in the last `q` slots. -/
noncomputable def orthogonalFormMatrix (p q : ℕ) (k : Type*) [Ring k] :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) k :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- A matrix `g` is form-preserving for the bilinear form matrix `F` when
`gᵀ F g = F`. -/
def IsFormPreserving {m : ℕ} {k : Type*} [CommRing k]
    (F g : Matrix (Fin m) (Fin m) k) : Prop :=
  g.transpose * F * g = F

end CoordinateExamples
