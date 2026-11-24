module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Projection
open Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SymmetricBilinearForms

/-- Two square matrices `M`, `N` over a commutative ring are *congruent* if
there exists an invertible matrix `A` such that `A * M * Aᵀ = N`. This is the
matrix-level equivalence relation underlying isometry of bilinear forms. -/
def MatrixCongruent {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M N : Matrix n n R) : Prop :=
  ∃ A : Matrix n n R, IsUnit A.det ∧ A * M * Aᵀ = N

/-- The matrix `H ⊕ ⟨1⟩` over `F₂`, formed by the hyperbolic plane and a
rank-one form with diagonal entry `1`. This is the model form used in
Claim 30.7. -/
def hyperbolicPlusIdentity : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

end SymmetricBilinearForms
