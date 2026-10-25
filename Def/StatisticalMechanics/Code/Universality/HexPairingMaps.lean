/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def hexPairing_classification_of_finiteCovering (R : HexFiniteRegion) (hdu : du ≠ 0)
    (pairs triplets : Finset ℕ)
    (pairBase pairLq pairLr tripBase : ℕ → List ℤ)
    (pairLq_sum : ∀ P ∈ pairs, (pairLq P).sum = -4)
    (pairLr_sum : ∀ P ∈ pairs, (pairLr P).sum = 4)
    (pairLen : ∀ P ∈ pairs, (pairLq P).length = (pairLr P).length)
    (pairQ_valid : ∀ P ∈ pairs,
      (ofTurns a h0 (pairBase P ++ pairLq P)).IsLegalSAW
        ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).StaysIn R.inRegion
        ∧ (ofTurns a h0 (pairBase P ++ pairLq P)).EndsAt (v + hexOmega * du))
    (pairR_valid : ∀ P ∈ pairs,
      (ofTurns a h0 (pairBase P ++ pairLr P)).IsLegalSAW
        ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).StaysIn R.inRegion
        ∧ (ofTurns a h0 (pairBase P ++ pairLr P)).EndsAt (v + hexOmega ^ 2 * du))
    (pairQ_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLq P) (v + du))
    (pairQ_passes_r : ∀ P ∈ pairs,
      PassesThrough a h0 (pairBase P ++ pairLq P) (v + hexOmega ^ 2 * du))
    (pairR_passes_p : ∀ P ∈ pairs, PassesThrough a h0 (pairBase P ++ pairLr P) (v + du))
    (pairR_passes_q : ∀ P ∈ pairs,
      PassesThrough a h0 (pairBase P ++ pairLr P) (v + hexOmega * du))
    (tripP_valid : ∀ T ∈ triplets,
      (ofTurns a h0 (tripBase T)).IsLegalSAW
        ∧ (ofTurns a h0 (tripBase T)).StaysIn R.inRegion
        ∧ (ofTurns a h0 (tripBase T)).EndsAt (v + du))
    (tripQ_valid : ∀ T ∈ triplets,
      (ofTurns a h0 (tripBase T ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (tripBase T ++ [-1])).StaysIn R.inRegion
        ∧ (ofTurns a h0 (tripBase T ++ [-1])).EndsAt (v + hexOmega * du))
    (tripR_valid : ∀ T ∈ triplets,
      (ofTurns a h0 (tripBase T ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (tripBase T ++ [1])).StaysIn R.inRegion
        ∧ (ofTurns a h0 (tripBase T ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
    (tripQ_not_passes_r : ∀ T ∈ triplets,
      ¬ PassesThrough a h0 (tripBase T ++ [-1]) (v + hexOmega ^ 2 * du))
    (tripR_not_passes_q : ∀ T ∈ triplets,
      ¬ PassesThrough a h0 (tripBase T ++ [1]) (v + hexOmega * du))
    (tripBase_inj : ∀ T1 T2 : triplets, tripBase T1 = tripBase T2 → T1 = T2)
    (pairQ_inj : ∀ P1 P2 : pairs,
      pairBase P1 ++ pairLq P1 = pairBase P2 ++ pairLq P2 → P1 = P2)
    (pairR_inj : ∀ P1 P2 : pairs,
      pairBase P1 ++ pairLr P1 = pairBase P2 ++ pairLr P2 → P1 = P2)
    (covp : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts)
    (covq : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T ∈ triplets, tripBase T ++ [-1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts))
    (covr : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T ∈ triplets, tripBase T ++ [1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts))
    (reindex :
      (((v + du) - v) * parafObservable R.inRegion a h0 (v + du) (5/8) hexChi
        + ((v + hexOmega * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi
        + ((v + hexOmega ^ 2 * du) - v) * parafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
      = (∑ P ∈ pairs,
          (((v + hexOmega * du) - v)
              * parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi (pairBase P ++ pairLq P)
            + ((v + hexOmega ^ 2 * du) - v)
                * parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (pairBase P ++ pairLr P)))
        + (∑ T ∈ triplets,
            (((v + du) - v) * parafSummand R.inRegion a h0 (v + du) (5/8) hexChi (tripBase T)
              + ((v + hexOmega * du) - v)
                  * parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi (tripBase T ++ [-1])
              + ((v + hexOmega ^ 2 * du) - v)
                  * parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tripBase T ++ [1])))) :
    HexSawClassification R.inRegion a h0 v du where
  pairs := pairs
  pairBase := pairBase
  pairLq := pairLq
  pairLr := pairLr
  pairLq_sum := pairLq_sum
  pairLr_sum := pairLr_sum
  pairLen := pairLen
  pairQ_valid := pairQ_valid
  pairR_valid := pairR_valid
  pairQ_passes_p := pairQ_passes_p
  pairQ_passes_r := pairQ_passes_r
  pairR_passes_p := pairR_passes_p
  pairR_passes_q := pairR_passes_q
  triplets := triplets
  tripBase := tripBase
  tripP_valid := tripP_valid
  tripQ_valid := tripQ_valid
  tripR_valid := tripR_valid
  tripQ_not_passes_r := tripQ_not_passes_r
  tripR_not_passes_q := tripR_not_passes_q
  tripBase_inj := tripBase_inj
  pairQ_inj := pairQ_inj
  pairR_inj := pairR_inj
  classify_p := R.classify_p_of_supportFinset_covering hdu triplets tripBase covp
  classify_q := R.classify_q_of_supportFinset_covering hdu pairs triplets pairBase pairLq tripBase covq
  classify_r := R.classify_r_of_supportFinset_covering hdu pairs triplets pairBase pairLr tripBase covr
  reindex := reindex


end StatMech.Universality
