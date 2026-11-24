module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingLatticeGreen.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointShell.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
open Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalAxisGreenComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

variable {d : Nat}

noncomputable def isingTorusNormalizedZeroMode
    (d : Nat) (beta : Real) (k : Nat) : Real :=
  (finiteTorusFourierCoeff
      (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
    Fintype.card (IsingDyadicTorus d k)

end StatMech.FrontierA
