/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part3
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

namespace PhysicalIsing

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def criticalFiniteBoxWeightedScaledCumulant
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real)
    (order : Nat) : Real :=
  scalarCumulantsOfMoments
    (fun m => criticalFiniteBoxWeightedFourthScale d n hd ^ m *
      finiteIsingWeightedRawMoment
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a m) order


end PhysicalIsing
end
end StatMech.FrontierA
