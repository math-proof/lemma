/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFull
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc8core.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion.Part2
import Def.StatisticalMechanics.Code.Walls.jc9core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc9_bdEdgeMatch_of_inputs (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z0 : Site 2} (h : jc9_InteriornessInputs K a z0) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
  obtain ⟨hExt, hz0K, hodd0, hInt⟩ := h
  exact jc9_bdEdgeMatch_of_windingWitness K a hExt hz0K hodd0 hInt


theorem jc9_inputs_realised_unitCell :
    pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  jc9_unitCell_bdEdgeMatch


end Walls
end StatMech
