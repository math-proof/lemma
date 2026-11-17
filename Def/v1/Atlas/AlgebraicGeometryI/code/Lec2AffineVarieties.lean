/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Sheaf
public import Class.v1.Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace


noncomputable section

universe u

/-- The natural ℕ-grading of `k[x₀, …, xₙ]` by total degree, used to define `ℙⁿ_k = Proj`. -/
def polynomialGrading (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

end
