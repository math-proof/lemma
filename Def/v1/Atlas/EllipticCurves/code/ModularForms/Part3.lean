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
public import Structure.v1.Atlas.EllipticCurves.code.ModularForms.Part3

@[expose] public section

open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


noncomputable section

namespace ModularityTheorem

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularEllipticCurve

/-- The L-function of a newform: the Dirichlet L-series with coefficients
`a_n ∈ ℂ`. -/
noncomputable def newformLFunction
    (f : IntegralWeight2Newform) (s : ℂ) : ℂ :=
  LSeries (fun n => (f.coeffs n : ℂ)) s

end ModularityTheorem
end
