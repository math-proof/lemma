/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityKernel.Part2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheCountingFunction
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) : Real :=
  (x + (∑ k, sixVertexTheta c x (p k)) / N) / (2 * Real.pi)

def sixVertexFiniteRootDensity
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) : Real :=
  (1 + (∑ k,
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
      sixVertexThetaDerivativeDenominator c x (p k)) / N) /
    (2 * Real.pi)

end
end StatMech.FrontierD
