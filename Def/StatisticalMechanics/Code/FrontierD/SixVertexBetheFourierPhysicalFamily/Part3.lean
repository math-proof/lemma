/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Mathlib.Topology.Homeomorph.Lemmas
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierPhysicalDensityFamily
    {a b : Real} (ha : 2 < a) :
    C(Set.Icc a b × Real, Real) :=
  ⟨fun z =>
      sixVertexFourierRootDensity
          (sixVertexAntiferroelectricLambda z.1.1)
          (sixVertexMomentumRapidityFamily (b := b) ha z) /
        (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2),
    continuous_sixVertexFourierPhysicalDensityFamily_fun ha⟩

end
end StatMech.FrontierD
