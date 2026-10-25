/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Onsager.InteriorRegion.Part2


namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


theorem mem_Lcells (q : Pt) :
    q ∈ Lcells ↔ (0 ≤ q.1 ∧ q.1 ≤ 3 ∧ 0 ≤ q.2 ∧ q.2 ≤ 3) ∧ ¬ (q.1 ≤ 1 ∧ q.2 ≤ 1) := by
  simp only [Lcells, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto


end StatMech.Onsager.InteriorRegion
