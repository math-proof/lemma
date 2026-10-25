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
import Def.StatisticalMechanics.Code.Onsager.WindingBridge.Part3


namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


theorem bset_subset (S : Set (Site 2)) :
    Bset S ⊆ preS S ∪ {p : Pt | toSite (p.1 + 1, p.2) ∈ S} := by
  intro p hp
  rw [Bset, Set.mem_setOf_eq, bdEdge_mk] at hp
  by_cases h : toSite p ∈ S
  · exact Or.inl h
  · refine Or.inr ?_
    by_contra hc
    exact h (hp.mpr hc)


theorem bset_finite (S : Set (Site 2)) (hfin : S.Finite) : (Bset S).Finite :=
  ((preS_finite S hfin).union (shiftPre_finite S hfin)).subset (bset_subset S)


end StatMech.Onsager.WindingBridge
