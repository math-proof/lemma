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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSechFourier
open Filter MeasureTheory Set Topology
open scoped FourierTransform


namespace StatMech.FrontierD

noncomputable section

def sixVertexSechProfile (lam x : Real) : Complex :=
  (Real.pi / (2 * lam) / Real.cosh (Real.pi ^ 2 * x / lam) : Real)

end
end StatMech.FrontierD
