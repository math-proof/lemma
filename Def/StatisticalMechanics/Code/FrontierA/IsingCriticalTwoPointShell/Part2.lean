/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointReduction
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointShell.Part2
open Finset MeasureTheory Set


namespace StatMech.FrontierA

open Ising Lattice Percolation Sharpness

open StatMech.FrontierB


def CriticalIsingMessagerMiracle (d : Nat) (hd : 1 ≤ d) : Prop :=
  ∀ n : Nat, 1 ≤ n →
    (∀ e ∈ boundaryEdges d (boxSV_boxF d n),
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d) e.1 ≤
        currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (criticalAxisSite hd n)) ∧
    ∀ x ∈ boxSV_vbF d n,
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (criticalAxisSite hd (d * n)) ≤
        currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d) x


end StatMech.FrontierA
