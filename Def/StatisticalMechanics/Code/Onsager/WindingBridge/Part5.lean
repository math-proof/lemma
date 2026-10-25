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
import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part4


namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


noncomputable def mkBoxData (S : Set (Site 2)) (hfin : S.Finite) : BoxData where
  B := (bset_finite S hfin).toFinset
  x1 := xBound S hfin
  hx1 := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    rcases bset_subset S hp with h | h
    · have hle := le_xBound S hfin (show toSite p ∈ S from h)
      simpa using hle
    · have hle := le_xBound S hfin (show toSite (p.1 + 1, p.2) ∈ S from h)
      have he : toSite (p.1 + 1, p.2) 0 = p.1 + 1 := by simp
      rw [he] at hle
      omega


end StatMech.Onsager.WindingBridge
