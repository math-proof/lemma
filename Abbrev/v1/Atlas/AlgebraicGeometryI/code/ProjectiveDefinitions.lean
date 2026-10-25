/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
open AlgebraicGeometry CategoryTheory

universe u


namespace ProjectiveDefinitions

/-- The standard grading on the polynomial ring `k[x_0, ..., x_n]` by total degree, where
`polynomialGrading k n d` is the `k`-submodule of homogeneous polynomials of degree `d`. -/
noncomputable abbrev polynomialGrading (k : Type u) [CommRing k] (n : ℕ) :
    ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

end ProjectiveDefinitions
