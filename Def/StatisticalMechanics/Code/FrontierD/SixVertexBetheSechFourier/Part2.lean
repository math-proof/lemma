/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSechFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part4
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier.Part2
open Filter MeasureTheory Set Topology
open scoped FourierTransform


namespace StatMech.FrontierD

noncomputable section

def sixVertexSechPhaseTerm
    (lam alpha : Real) (n : Int) : Complex :=
  ((1 / (2 * Real.cosh ((n : Real) * lam)) : Real) : Complex) *
    fourier n ((alpha / (2 * Real.pi) : Real) : UnitAddCircle)

end
end StatMech.FrontierD
