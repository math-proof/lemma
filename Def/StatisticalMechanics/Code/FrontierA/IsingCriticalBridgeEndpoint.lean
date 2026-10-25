/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part8
open Filter Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice

noncomputable section

noncomputable def oddPrismCriticalLowerHalfBridgeMeanDensity
    (n : Nat) : Real := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  exact replicaBridgeMean (oddPrismLowerHalfGraph n)
      (fun _ => Ising.betaC 3)
      (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
      (oddPrismLowerHalfBridgeSites n) 0 /
    (((2 * n + 1 : Nat) : Real) ^ 2)


end
end StatMech.FrontierA
