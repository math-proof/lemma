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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ProjectiveDefinitions
open AlgebraicGeometry CategoryTheory

universe u


namespace ProjectiveDefinitions

/-- The polynomial ring `k[x_0, ..., x_n]` is a graded ring under the total-degree
grading. -/
noncomputable instance polynomialGradedAlgebra (k : Type u) [CommRing k] (n : ℕ) :
    GradedRing (polynomialGrading k n) :=
  MvPolynomial.gradedAlgebra

end ProjectiveDefinitions
