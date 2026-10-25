/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/KernelDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Lemma.Fin.Nondegenerate.of.EqOrthogonalBilinFormTop_Bot.IsRefl
set_option maxHeartbeats 0


namespace Formalization.GeometricAlgebra

open LinearMap.BilinForm

variable {k : Type*} [Field k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The radical of a subspace `W` for the bilinear form `B`: the part of `W`
that is orthogonal to all of `W`. -/
def SubspaceRadical (B : LinearMap.BilinForm k V) (W : Submodule k V) : Submodule k V :=
  W ⊓ orthogonal B W

set_option linter.unusedSectionVars false in

/-- A hyperbolic pair for `B` consists of two isotropic vectors `x, y` with
`B x y = 1`. -/
def IsHyperbolicPair (B : LinearMap.BilinForm k V) (x y : V) : Prop :=
  B x x = 0 ∧ B y y = 0 ∧ B x y = 1

set_option linter.unusedSectionVars false in
/-- A subspace `S` is a hyperbolic space for `B` if it is spanned by a finite
collection of mutually orthogonal hyperbolic pairs `{x_i, y_i}`. -/
def IsHyperbolicSpace (B : LinearMap.BilinForm k V) (S : Submodule k V) : Prop :=
  ∃ (n : ℕ) (x y : Fin n → V),
    (∀ i, IsHyperbolicPair B (x i) (y i)) ∧
    (∀ i j, i ≠ j → B (x i) (x j) = 0 ∧ B (x i) (y j) = 0 ∧ B (y i) (y j) = 0) ∧
    S = Submodule.span k (Set.range x ∪ Set.range y)

end Formalization.GeometricAlgebra
