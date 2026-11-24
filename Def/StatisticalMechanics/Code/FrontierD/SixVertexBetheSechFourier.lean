module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part4
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier
open Filter MeasureTheory Set Topology
open scoped FourierTransform


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexSechProfile (lam x : Real) : Complex :=
  (Real.pi / (2 * lam) / Real.cosh (Real.pi ^ 2 * x / lam) : Real)

end
end StatMech.FrontierD
