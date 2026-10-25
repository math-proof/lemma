/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailCauchy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailConvolution.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexTailConvolutionError (c : Real) (N : Nat) : Real :=
  sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) *
        (2 * Real.pi)

def sixVertexFiniteConvolutionDefect
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) : Real :=
  (∑ j, sixVertexRootDensityKernel c x (p j)) / N -
    ∫ y in -Real.pi..Real.pi,
      sixVertexRootDensityKernel c x y *
        sixVertexFiniteRootDensity c N n p y

end
end StatMech.FrontierD
