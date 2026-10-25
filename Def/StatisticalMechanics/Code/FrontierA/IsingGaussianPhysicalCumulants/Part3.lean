/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part2
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

namespace PhysicalIsing

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def criticalFiniteBoxWeightedFourthScale
    (d n : Nat) (hd : 2 <= d) : Real :=
  Classical.choose (exists_criticalFiniteBoxWeightedFourthScale d n hd)

end PhysicalIsing
end
end StatMech.FrontierA
