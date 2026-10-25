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
import Abbrev.v1.Atlas.EllipticCurves.code.ModularForms.Part4
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


namespace SpectralTheorem

open LinearMap IsSymmetric Module.End

/-- The normalized (completed) L-function of an elliptic curve over `ℚ`:
`N^{s/2} (2π)^{-s} Γ(s) L(E, s)`. -/
noncomputable def cuspFormDataOfNewform (f : IntegralWeight2Newform) : CuspFormData where
  weight := 2
  level := f.level
  coeffs := fun n => (f.coeffs n : ℂ)
  coeffs_zero := by simp [f.coeffs_zero]

end SpectralTheorem
