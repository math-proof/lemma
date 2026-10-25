/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityCriticalAxisClosure
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPhaseEndpoint
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

def criticalTorusLocalSpinProd (d : Nat) (A : Finset (Site d))
    (n : Nat) : Real :=
  expJ (isingTorusGraph d n).edgeFinset
    (fun _ ↦ IsingFK.betaC (magnetization d)) (fun _ ↦ 0)
    (spinProd (A.image (isingSiteToDyadicTorus n)))

end
end StatMech.FrontierA
