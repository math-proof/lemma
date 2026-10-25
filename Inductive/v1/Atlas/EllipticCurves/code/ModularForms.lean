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
import Structure.v1.Atlas.EllipticCurves.code.ModularForms.Part2
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold


noncomputable section

namespace EllipticCurveReduction

open MinimalModel

/-- The four possible reduction types of an elliptic curve at a prime:
good reduction, split multiplicative reduction, nonsplit multiplicative reduction,
or additive reduction. -/
inductive ReductionType where
  | good : ReductionType
  | splitMultiplicative : ReductionType
  | nonsplitMultiplicative : ReductionType
  | additive : ReductionType
  deriving DecidableEq, Repr

end EllipticCurveReduction
end
