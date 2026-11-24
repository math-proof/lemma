module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointReduction
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointShell
open Finset MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Ising Lattice Percolation Sharpness

open StatMech.FrontierB


def criticalAxisSite {d : Nat} (hd : 1 ≤ d) (n : Nat) : Site d :=
  fun i => if i = (⟨0, hd⟩ : Fin d) then (n : Int) else 0

end StatMech.FrontierA
