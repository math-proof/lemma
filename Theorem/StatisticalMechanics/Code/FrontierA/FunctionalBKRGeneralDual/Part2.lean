/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual.Part3
import Theorem.StatisticalMechanics.Code.Walls.rb3reimerclose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc4_core
import Theorem.StatisticalMechanics.Code.Walls.rc3_keyflipinvolutive
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

open StatMech.Walls

open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in


theorem dualOccurrence_to_twisted_box {A B : Set (ConfigSpace E)}
    {p : ConfigSpace E × ConfigSpace E}
    {k : ConfigSpace E × ConfigSpace E}
    (hp : p ∈ dualDisjointOccurrence A B) (hpk : orbitKey p = k) :
    p.1 ∈ disjointOccurrence A (kssTwist k B) := by
  obtain ⟨K, L, hKL, hA, hB⟩ := hp
  refine ⟨K, L, hKL, hA, ?_⟩
  intro tau htau
  change poc_keyFlip k tau ∈ B
  apply hB
  intro e he
  have heq := htau e he
  have hsnd := poc_snd_eq p k hpk
  rw [hsnd]
  simp only [poc_keyFlip, poc_flip]
  split <;> simp_all


theorem rb3_slabCardAll : poc_SlabCardAll := by
  apply rc4_residue_of_reimerCardFormAll
  apply rc17_reimerCardFormAll_of_nonMonotone
  apply rc18_nonMonotone_of_cylBoxReflInter
  exact rc20_cylBoxReflInter_of_famCylBoxResidue rb3_famCylBoxResidue


theorem imgOrbit_twist_eq_diagonalOrbit (A B : Set (ConfigSpace E))
    (k : ConfigSpace E × ConfigSpace E) :
    imgOrbit A (kssTwist k B) k = kssDiagonalOrbit A B k := by
  classical
  ext p
  simp only [imgOrbit, kssDiagonalOrbit, Finset.mem_filter,
    Finset.mem_univ, true_and, kssTwist, Set.mem_setOf_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hpA, hpB, hpk⟩
    have hsnd := poc_snd_eq p k hpk
    rw [hsnd, rc3_keyFlip_keyFlip] at hpB
    exact ⟨⟨hpA, hpB⟩, hpk⟩
  · rintro ⟨⟨hpA, hpB⟩, hpk⟩
    have hsnd := poc_snd_eq p k hpk
    rw [hsnd, rc3_keyFlip_keyFlip]
    exact ⟨hpA, hpB, hpk⟩


theorem kssDualOrbit_card_le {n : ℕ}
    (A B : Set (ConfigSpace (Fin n)))
    (k : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    #(kssDualOrbit A B k) ≤ #(kssDiagonalOrbit A B k) := by
  classical
  calc
    #(kssDualOrbit A B k) ≤ #(boxOrbit A (kssTwist k B) k) := by
      apply Finset.card_le_card
      intro p hp
      simp only [kssDualOrbit, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨dualOccurrence_to_twisted_box hp.1 hp.2, hp.2⟩
    _ ≤ #(imgOrbit A (kssTwist k B) k) :=
      ((poc_perOrbitCard_iff_slabCard A (kssTwist k B)).mpr
        (rb3_slabCardAll n A (kssTwist k B))) k
    _ = #(kssDiagonalOrbit A B k) := by
      rw [imgOrbit_twist_eq_diagonalOrbit]

omit [DecidableEq E] in


theorem pairWeight_eq_of_sameOrbit (phi : E → Bool → ℝ)
    {p q : ConfigSpace E × ConfigSpace E} (h : sameOrbit p q) :
    pweight phi q.1 * pweight phi q.2 =
      pweight phi p.1 * pweight phi p.2 := by
  rw [swapPair_eq_of_sameOrbit p q h]
  simp only [swapPair_fst, swapPair_snd]
  exact swapPair_weight phi _ p.1 p.2


end StatMech.FrontierA
