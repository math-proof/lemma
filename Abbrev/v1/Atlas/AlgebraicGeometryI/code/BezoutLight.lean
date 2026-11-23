/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutLight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
@[expose] public section

set_option maxHeartbeats 400000

open MvPolynomial


/-- The degree-`n` piece of the homogeneous quotient ring `k[x₀, x₁, x₂] / I`, presented as the
quotient of the space of degree-`n` homogeneous polynomials by the corresponding piece of `I`. -/
noncomputable abbrev homogQuotPiece (k : Type*) [Field k]
    (I : Ideal (MvPolynomial (Fin 3) k)) (n : ℕ) :=
  (homogeneousSubmodule (Fin 3) k n) ⧸
    Submodule.comap (homogeneousSubmodule (Fin 3) k n).subtype (I.restrictScalars k)

