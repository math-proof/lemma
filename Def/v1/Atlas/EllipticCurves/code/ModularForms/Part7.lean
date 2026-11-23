/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.FermatsLastTheorem
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Abbrev.v1.Atlas.EllipticCurves.code.ModularForms.Part4

@[expose] public section

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
