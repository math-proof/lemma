/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Bivariate
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial


noncomputable section

open Polynomial Classical

/-- Typeclass-level commutative group instance on `cl(𝒪)`. -/
noncomputable instance (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    CommGroup (ImagQuadIdealClass D hD) := instCommGroupImagQuadIdealClass D hD

end
