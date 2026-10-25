/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part14
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheTupleBoltzmann {n : Nat} (N : Nat) (c : Real)
    (x q : Fin (n + 1) -> Int) : Complex :=
  ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card

def sixVertexBetheTupleWaveWeight {n : Nat} (N : Nat) (c : Real)
    (p : Fin (n + 1) -> Real) (x q : Fin (n + 1) -> Int) : Complex :=
  sixVertexBetheTupleBoltzmann N c x q *
    sixVertexCoordinateBetheIntWave c p q

end
end StatMech.FrontierD
