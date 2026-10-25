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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledNormalizedAmplitude (k : Nat) (c : Real)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) : Complex :=
  (((Equiv.Perm.sign sigma : Int) : Complex)) *
    ∏ i, ∏ j ∈ Finset.Ioi i,
      sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase
          (sixVertexHalfFilledBetheRootAt k (sigma i) c))
        (sixVertexBethePhase
          (sixVertexHalfFilledBetheRootAt k (sigma j) c))

end
end StatMech.FrontierD
