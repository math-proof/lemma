/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def abblResidualEvent (d n : Nat) :
    Set (ConfigSpace (Sym2 (Option (sctBox d n)))) :=
  connEvent (withGhost (sctBoxGraph d n)) Set.univ
      (some (sctBoxOrigin d n)) (abbTarget d n) ∩
    (connEvent (withGhost (sctBoxGraph d n)) Set.univ
      (some (sctBoxOrigin d n)) {none})ᶜ


end Sharpness
end StatMech
