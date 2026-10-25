/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeEndpoint
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part2


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Filter Topology

noncomputable section

def oddPrismCriticalUnequalBridgeMeanDensity (n : Nat) : Real :=
  unequalReplicaBridgeMean
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0 /
    (((2 * n + 1 : Nat) : Real) ^ 2)

end
end StatMech.FrontierA
