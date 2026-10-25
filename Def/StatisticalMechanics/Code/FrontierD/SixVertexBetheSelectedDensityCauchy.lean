/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailSelectedDensity
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSelectedDensityCauchyError (c : Real) (k l : Nat) : Real :=
  ((sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) +
      sixVertexTailConvolutionError c (sixVertexFourWidth 0 l)) /
    (2 * Real.pi)) /
      (1 - sixVertexRootDensityContractionRate c)


def sixVertexSelectedEmpiricalObservable
    {c : Real} (hc : 2 < c) (f : Real -> Real) (k : Nat) : Real :=
  (∑ j, f (sixVertexHalfFilledBetheRoots hc k j)) /
    (sixVertexFourWidth 0 k : Real)


def sixVertexSelectedObservableQuadratureError
    (c : Real) (C : NNReal) (k : Nat) : Real :=
  (C : Real) * sixVertexFiniteRootDensityUniformBound c *
    (1 / ((sixVertexFourWidth 0 k : Real) *
      sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi)


def sixVertexSelectedObservableCauchyControl
    (c : Real) (C : NNReal) (B : Real) (k : Nat) : Real :=
  sixVertexSelectedObservableQuadratureError c C k +
    B * (((sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) /
      (2 * Real.pi)) /
        (1 - sixVertexRootDensityContractionRate c)) /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi)


end
end StatMech.FrontierD
