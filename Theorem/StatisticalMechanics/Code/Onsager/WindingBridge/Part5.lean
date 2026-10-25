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
import Def.StatisticalMechanics.Code.Onsager.WindingBridge.Part5


namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


theorem boundedRight (S : Set (Site 2)) (hfin : S.Finite) :
    BoundedRight (mkBoxData S hfin) (preS S) := by
  intro p hp
  have hle := le_xBound S hfin (show toSite p ∈ S from hp)
  simpa [mkBoxData] using hle


theorem boundaryCovers (S : Set (Site 2)) (hfin : S.Finite) :
    BoundaryCoversTransitions (mkBoxData S hfin) (preS S) := by
  intro p hne
  refine Or.inl ?_
  have hchg : ¬ (toSite p ∈ S ↔ toSite (p.1 + 1, p.2) ∈ S) := hne
  have hbd := barrier_of_side_change S (toSite_adj_shift p) hchg
  show p ∈ (bset_finite S hfin).toFinset
  rw [Set.Finite.mem_toFinset]
  exact hbd


theorem interiorReaches_of_cluster (S : Set (Site 2)) (hfin : S.Finite) (w : Pt)
    (hin : toSite (rayX w 1) ∈ S) :
    InteriorReaches (mkBoxData S hfin) w :=
  interiorReaches_of_polygon (mkBoxData S hfin) w (preS S)
    (boundedRight S hfin) (boundaryCovers S hfin) hin


theorem chord_of_cluster (S : Set (Site 2)) (hfin : S.Finite) (w : Pt)
    (hw : w ∈ (mkBoxData S hfin).B) (hin : toSite (rayX w 1) ∈ S) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ (mkBoxData S hfin).B ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ (mkBoxData S hfin).B) :=
  chord_of_interiorReaches (mkBoxData S hfin) w hw (interiorReaches_of_cluster S hfin w hin)

end StatMech.Onsager.WindingBridge
