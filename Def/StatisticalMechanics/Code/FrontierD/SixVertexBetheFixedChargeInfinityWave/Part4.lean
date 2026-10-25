/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part3
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeLimitingPhaseStep (r k : Nat) : Complex :=
  Complex.exp (Complex.I *
    (2 * Real.pi / (sixVertexFixedChargeBetheComplementCount r k : Real)))


def sixVertexFixedChargeLimitingPhaseCenter (r k : Nat) : Complex :=
  Complex.exp (-Complex.I *
    (Real.pi *
      (sixVertexFixedChargeBetheParticleCount r k - 1 : Nat) /
        (sixVertexFixedChargeBetheComplementCount r k : Real)))

end
end StatMech.FrontierD
