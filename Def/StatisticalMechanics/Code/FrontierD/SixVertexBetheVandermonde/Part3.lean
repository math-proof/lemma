/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part3
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledNormalizedOddWave (k : Nat) (c : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin ((k + 1) + (k + 1))),
    sixVertexHalfFilledNormalizedAmplitude k c sigma *
      sixVertexBetheMonomial
        (fun j => sixVertexHalfFilledBetheRootAt k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega))


def sixVertexHalfFilledVandermondeSum (k : Nat) : Complex :=
  ∑ sigma : Equiv.Perm (Fin ((k + 1) + (k + 1))),
    (((Equiv.Perm.sign sigma : Int) : Complex)) *
      (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexHalfFilledLimitingPhase k (sigma i)) *
      ∏ i, sixVertexHalfFilledLimitingPhase k (sigma i) ^
        (2 * i.val + 1)

end
end StatMech.FrontierD
