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
import Structure.v1.Atlas.EllipticCurves.code.ModularForms.Part5
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


namespace NewformDefinition

open Complex Asymptotics Filter

/-- The value at `s` of a Dirichlet series, defined as the L-series of its
coefficient sequence. -/
noncomputable def DirichletSeries.eval (L : DirichletSeries) (s : ℂ) : ℂ :=
  LSeries L.coeffs s

/-- Summability of a Dirichlet series at `s`: the underlying L-series sum is
summable. -/
def DirichletSeries.summable (L : DirichletSeries) (s : ℂ) : Prop :=
  LSeriesSummable L.coeffs s

/-- The arithmetic rank of an elliptic curve over `ℚ`: the ℤ-rank of its
Mordell–Weil group modulo torsion. -/
noncomputable def arithmeticRank (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℕ :=
  Module.finrank ℤ (E.Point ⧸ AddCommGroup.torsion E.Point)

end NewformDefinition
