/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityOddInsertion.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FinitePlusBoundarySwitchingBridge
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Instance.StatisticalMechanics.Code.FrontierB.CurrentContinuityBoxInfluence
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Finset Sharpness Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boxCurrentEdgeOfAdjacent
    {d n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n)
    (hxy : (hypercubicLattice d).Adj x y) :
    (StatMech.FK.boxGraph d n).edgeFinset :=
  ⟨s((⟨x, hx⟩ : StatMech.FK.boxVerts d n), ⟨y, hy⟩),
    StatMech.FK.boxEdge_mem n _ x y hxy (by rfl)⟩

end StatMech.FrontierB
