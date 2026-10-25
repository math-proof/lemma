/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Class.v1.Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties
open AlgebraicGeometry CategoryTheory TopologicalSpace


noncomputable section

universe u

/-- The natural ℕ-grading of `k[x₀, …, xₙ]` by total degree, used to define `ℙⁿ_k = Proj`. -/
def polynomialGrading (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

end
