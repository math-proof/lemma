/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part6
import Def.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


theorem phb_doubleDual_component_card (K : Set (Site 2)) :
    Nat.card (whb_faceRegion (faceBoundaryGraph K)).ConnectedComponent =
      Nat.card (latticeMinusBarrier K).ConnectedComponent := by
  exact Nat.card_congr (phb_doubleDualIso K).connectedComponentEquiv.symm


theorem phb_faceBoundaryGraph_support_finite (K : Set (Site 2)) (hK : K.Finite) :
    (faceBoundaryGraph K).support.Finite := by
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph K hK
  exact T.finite_toSet.subset hT


end Lattice
end StatMech
