/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jbc_reduced_of_directions (P : PlanarZ2Subgraph)
    (hcyc : jbc_CycleDirection P) (hbr : jbc_BridgeDirection P) :
    jbc_ReducedBridgeCycle P := by
  intro K hKle x y hadjG hnotK
  constructor
  · intro hr; exact hcyc K hKle hadjG hnotK hr
  · intro hnr; by_contra hcon; exact hnr (hbr K hKle hadjG hnotK hcon)


end Lattice
end StatMech
