/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochDedekind.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology

open scoped TensorProduct
open nonZeroDivisors
open RiemannRochCurves DedekindCurve
open UniqueFactorizationMonoid

noncomputable section

namespace RiemannRochDedekind


/-- `H^1` of the structure sheaf for a Dedekind curve, repackaged at the
top-level of this namespace. -/
def h1_O (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  DedekindCurve.h1_O k A

/-- `H^1` of a skyscraper sheaf on a Dedekind curve, repackaged. -/
def h1_sky (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  DedekindCurve.h1_sky k A
