/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part11


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decRootedAtomExponent_eq_atoms_sum
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decRootedAtomExponent root =
      ((ons_decRootedAtomEquivNonemptyAtoms L d root).1.map
        ons_decFirstReturnAtomExponent).sum := by
  have hexponent := ons_decLoopExponent_eq_firstReturnFactors_sum
    L d root.2.1 root.2.2.1
  change ons_decRootedAtomExponent root =
      ((ons_firstReturnFactors d (ons_decRootedAtomList root)).map
        (ons_pathSum (ons_decTransitionExponent L))).sum at hexponent
  rw [← ons_decRootedAtomEquivNonemptyAtoms_segments L d root]
    at hexponent
  let atoms := (ons_decRootedAtomEquivNonemptyAtoms L d root).1
  have hmap :
      atoms.map
          (ons_pathSum (ons_decTransitionExponent L) ∘
            ons_decFirstReturnAtomSegment) =
        atoms.map ons_decFirstReturnAtomExponent := by
    apply List.map_congr_left
    intro atom hatom
    exact ons_decFirstReturnAtom_exponent_segment L d atom
  simp only [ons_decFirstReturnAtomsSegments, List.map_map] at hexponent
  dsimp only [atoms] at hmap
  rw [hmap] at hexponent
  exact hexponent

theorem ons_decRootedAtomWeight_eq_atoms_prod
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decRootedAtomWeight L a b root =
      ((ons_decRootedAtomEquivNonemptyAtoms L d root).1.map
        (ons_decFirstReturnAtomWeight L a b)).prod := by
  have hweight := ons_decLoopScalar_eq_firstReturnFactors_prod
    L a b d root.2.1 root.2.2.1
  change ons_decRootedAtomWeight L a b root =
      ((ons_firstReturnFactors d (ons_decRootedAtomList root)).map
        (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)))).prod
    at hweight
  rw [← ons_decRootedAtomEquivNonemptyAtoms_segments L d root]
    at hweight
  let atoms := (ons_decRootedAtomEquivNonemptyAtoms L d root).1
  have hmap :
      atoms.map
          (ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ ↦ 1)
              ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) ∘
            ons_decFirstReturnAtomSegment) =
        atoms.map (ons_decFirstReturnAtomWeight L a b) := by
    apply List.map_congr_left
    intro atom hatom
    exact ons_decFirstReturnAtom_weight_segment L a b d atom
  simp only [ons_decFirstReturnAtomsSegments, List.map_map] at hweight
  dsimp only [atoms] at hmap
  rw [hmap] at hweight
  exact hweight

theorem ons_decRootedAtom_atoms_length_eq_visitCount
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    (ons_decRootedAtomEquivNonemptyAtoms L d root).1.length =
      ons_visitCount d root.2.1 := by
  have hlength := ons_firstReturnFactors_length
    d root.2.1 root.2.2.1
  change (ons_firstReturnFactors d
      (ons_decRootedAtomList root)).length =
    ons_visitCount d root.2.1 at hlength
  rw [← ons_decRootedAtomEquivNonemptyAtoms_segments L d root]
    at hlength
  simpa only [ons_decFirstReturnAtomsSegments, List.length_map]
    using hlength

theorem ons_decRootedAtom_externalExponent_eq_visitCount
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (root : ons_DecRootedAtom L d) :
    ons_decRootedAtomExponent root s(d, ons_dartRev L d) =
      ons_visitCount d root.2.1 := by
  rw [ons_decRootedAtomExponent,
    ons_decLoopExponent_external_apply,
    ons_visitCount_eq_card_filter]
  have hterm : ∀ k,
      (if root.2.1 k = d ∨ root.2.1 k = ons_dartRev L d then 1 else 0) =
        if root.2.1 k = d then 1 else 0 := by
    intro k
    by_cases hk : root.2.1 k = d
    · simp [hk]
    · simp [hk, root.2.2.2 k]
  simp_rw [hterm]
  rw [Finset.sum_boole]
  simp

end StatMech.Onsager
