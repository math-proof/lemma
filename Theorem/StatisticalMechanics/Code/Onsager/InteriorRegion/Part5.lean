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
import Def.StatisticalMechanics.Code.Onsager.InteriorRegion.Part5


namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


theorem interior_iff_odd_crossing (S : Set (Site 2)) (p : Pt) (N : ℕ)
    (hout : toSite (rayX p N) ∉ S) :
    toSite p ∈ S ↔ ¬ Even (crossCount S (rayWalk p N)) := by
  have h := crossCount_parity S (rayWalk p N)
  constructor
  · intro hp hev
    exact hout ((h.mp hev).mp hp)
  · intro hne
    by_contra hp
    apply hne
    rw [h]
    constructor
    · intro hp'; exact absurd hp' hp
    · intro hz; exact absurd hz hout


end StatMech.Onsager.InteriorRegion
