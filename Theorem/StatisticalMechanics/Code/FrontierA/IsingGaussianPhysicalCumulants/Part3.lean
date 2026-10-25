/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part3
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

namespace PhysicalIsing

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem criticalFiniteBoxWeightedFourthScale_pos
    (d n : Nat) (hd : 2 <= d) :
    0 < criticalFiniteBoxWeightedFourthScale d n hd :=
  (Classical.choose_spec
    (exists_criticalFiniteBoxWeightedFourthScale d n hd)).1

theorem criticalFiniteBoxWeightedFourthScale_pow_four
    (d n : Nat) (hd : 2 <= d) :
    criticalFiniteBoxWeightedFourthScale d n hd ^ 4 = 1 /
      (2 * (Fintype.card (sctBox d n) : Real) *
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
        ((2 * n + 1 : Nat) : Real) ^ d) :=
  (Classical.choose_spec
    (exists_criticalFiniteBoxWeightedFourthScale d n hd)).2


end PhysicalIsing
end
end StatMech.FrontierA
