/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part4


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexConcrete_classification (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    HexSawClassification (hexConcrete_region a h0 hclosure).inRegion a h0
      (hexConcreteV a h0) (hexConcreteDu a h0) :=
  hexPairing_classification_of_finiteCovering (hexConcrete_region a h0 hclosure)
    (hexConcreteDu_ne a h0)
    (pairs := ∅) (triplets := {0})
    (pairBase := fun _ => []) (pairLq := fun _ => []) (pairLr := fun _ => [])
    (tripBase := fun _ => [])
    (pairLq_sum := by simp) (pairLr_sum := by simp) (pairLen := by simp)
    (pairQ_valid := by simp) (pairR_valid := by simp)
    (pairQ_passes_p := by simp) (pairQ_passes_r := by simp)
    (pairR_passes_p := by simp) (pairR_passes_q := by simp)
    (tripP_valid := fun _ _ =>
      ⟨(hexConcrete_atoms a h0).1.1, hexConcrete_staysIn_p a h0 hclosure,
        (hexConcrete_atoms a h0).1.2⟩)
    (tripQ_valid := fun _ _ => by
      simpa using ⟨(hexConcrete_atoms a h0).2.1.1, hexConcrete_staysIn_q a h0 hclosure,
        (hexConcrete_atoms a h0).2.1.2⟩)
    (tripR_valid := fun _ _ => by
      simpa using ⟨(hexConcrete_atoms a h0).2.2.1.1, hexConcrete_staysIn_r a h0 hclosure,
        (hexConcrete_atoms a h0).2.2.1.2⟩)
    (tripQ_not_passes_r := fun _ _ => by simpa using (hexConcrete_atoms a h0).2.2.2.1)
    (tripR_not_passes_q := fun _ _ => by simpa using (hexConcrete_atoms a h0).2.2.2.2)
    (tripBase_inj := by
      rintro ⟨T1, hT1⟩ ⟨T2, hT2⟩ _
      simp only [Finset.mem_singleton] at hT1 hT2
      subst hT1; subst hT2; rfl)
    (pairQ_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (pairR_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (covp := by
      intro ts hts hp
      refine ⟨0, by simp, ?_⟩
      exact (hexConcrete_covering_p a h0 hclosure ts
        (((hexConcrete_region a h0 hclosure).mem_supportFinset (hexConcreteDu_ne a h0) ts).mp hts)
        hp).symm)
    (covq := by
      intro ts hts hq
      refine Or.inl ⟨0, by simp, ?_⟩
      simpa using (hexConcrete_covering_q a h0 hclosure ts
        (((hexConcrete_region a h0 hclosure).mem_supportFinset (hexConcreteDu_ne a h0) ts).mp hts)
        hq).symm)
    (covr := by
      intro ts hts hr
      refine Or.inl ⟨0, by simp, ?_⟩
      simpa using (hexConcrete_covering_r a h0 hclosure ts
        (((hexConcrete_region a h0 hclosure).mem_supportFinset (hexConcreteDu_ne a h0) ts).mp hts)
        hr).symm)
    (reindex := by
      rw [Finset.sum_empty, Finset.sum_singleton, zero_add]
      rw [hexConcrete_obs_p a h0 hclosure, hexConcrete_obs_q a h0 hclosure,
        hexConcrete_obs_r a h0 hclosure]
      simp)


end StatMech.Universality
