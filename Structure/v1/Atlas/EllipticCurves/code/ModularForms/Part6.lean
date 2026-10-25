/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FermatsLastTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Analytic.Order
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.EllipticCurves.code.ModularForms.Part5
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


namespace HeckeAnalyticContinuation

open Complex

/-- Data for a cusp form: weight, level, and complex Fourier coefficients with
`a_0 = 0`. -/
structure CuspFormData where
  weight : ℕ
  level : ℕ+
  coeffs : ℕ → ℂ
  coeffs_zero : coeffs 0 = 0

/-- The L-function attached to a cusp form's coefficient data: the Dirichlet
L-series of its coefficients. -/

end HeckeAnalyticContinuation

namespace EulerProductNewform

open Complex HeckeAnalyticContinuation

/-- Data for a normalized newform: cusp-form data together with the
normalization `a_1 = 1`. -/
structure NewformData extends CuspFormData where
  coeffs_one : toCuspFormData.coeffs 1 = 1

end EulerProductNewform
