module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
public import Mathlib.LinearAlgebra.Vandermonde
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part2
open Finset Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
