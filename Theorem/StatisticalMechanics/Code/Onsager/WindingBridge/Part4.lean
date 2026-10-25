/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.InteriorReaches
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Onsager.WindingBridge.Part4


namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


theorem le_xBound (S : Set (Site 2)) (hfin : S.Finite) {x : Site 2} (hx : x ∈ S) :
    x 0 ≤ xBound S hfin :=
  (hfin.image (fun x : Site 2 => x 0)).bddAbove.choose_spec ⟨x, hx, rfl⟩


end StatMech.Onsager.WindingBridge
