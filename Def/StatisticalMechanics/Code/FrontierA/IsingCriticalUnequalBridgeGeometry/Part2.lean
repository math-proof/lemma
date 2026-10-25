/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeEndpoint
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Filter Topology

noncomputable section

def oddPrismCriticalLowerHalfSpinAverage (n : Nat) : Real :=
  (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      oddPrismLowerHalfSurfaceSpinMeanAt (Ising.betaC 3) n q.1 q.2) /
    (((2 * n + 1 : Nat) : Real) ^ 2)

end
end StatMech.FrontierA
