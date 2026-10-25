/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def hexPairing_emptySupport_classification (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    HexSawClassification (hexFiniteRegion_single a w hclosure).inRegion a h0 v du :=
  hexPairing_classification_of_finiteCovering
    (hexFiniteRegion_single a w hclosure) hdu
    (pairs := ∅) (triplets := ∅)
    (pairBase := fun _ => []) (pairLq := fun _ => []) (pairLr := fun _ => [])
    (tripBase := fun _ => [])
    (pairLq_sum := by simp) (pairLr_sum := by simp) (pairLen := by simp)
    (pairQ_valid := by simp) (pairR_valid := by simp)
    (pairQ_passes_p := by simp) (pairQ_passes_r := by simp)
    (pairR_passes_p := by simp) (pairR_passes_q := by simp)
    (tripP_valid := by simp) (tripQ_valid := by simp) (tripR_valid := by simp)
    (tripQ_not_passes_r := by simp) (tripR_not_passes_q := by simp)
    (tripBase_inj := by rintro ⟨T1, hT1⟩; exact absurd hT1 (by simp))
    (pairQ_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (pairR_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp))
    (covp := by
      intro ts hts _
      exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
        (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts))
    (covq := by
      intro ts hts _
      exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
        (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts))
    (covr := by
      intro ts hts _
      exact absurd ((((hexFiniteRegion_single a w hclosure).mem_supportFinset hdu ts).mp hts))
        (hexPairing_emptySupport a w h0 v du hdu hclosure hap haq har ts))
    (reindex := by
      rw [Finset.sum_empty, Finset.sum_empty, add_zero]
      
      rw [hexPairing_emptySupport_observable_zero a w h0 (v + du) (5/8) hexChi hclosure hap,
          hexPairing_emptySupport_observable_zero a w h0 (v + hexOmega * du) (5/8) hexChi hclosure haq,
          hexPairing_emptySupport_observable_zero a w h0 (v + hexOmega ^ 2 * du) (5/8) hexChi hclosure har]
      ring)


end StatMech.Universality
