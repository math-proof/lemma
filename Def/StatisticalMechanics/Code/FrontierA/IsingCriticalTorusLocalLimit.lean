module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryMonomialComparison.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityCriticalAxisClosure
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
public import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPhaseEndpoint
open Filter Finset MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

def boxFinsetSpinSupport (d n : Nat) (A : Finset (Site d)) :
    Finset {x : Site d // x ∈ boxFinset d n} :=
  Finset.univ.filter fun x ↦ x.1 ∈ A

end
end StatMech.FrontierA
