/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexSeparation.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexVertexCoverage
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


def singleTriplet (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ) (tb : List ℤ)
    (hp : (ofTurns a h0 tb).IsLegalSAW ∧ (ofTurns a h0 tb).StaysIn region
        ∧ (ofTurns a h0 tb).EndsAt (v + du))
    (hq : (ofTurns a h0 (tb ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [-1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (tb ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (tb ++ [1])).StaysIn region
        ∧ (ofTurns a h0 (tb ++ [1])).EndsAt (v + hexOmega ^ 2 * du))
    (hQr : ¬ PassesThrough a h0 (tb ++ [-1]) (v + hexOmega ^ 2 * du))
    (hRq : ¬ PassesThrough a h0 (tb ++ [1]) (v + hexOmega * du))
    (hcp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → tb = ts)
    (hcq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) → tb ++ [-1] = ts)
    (hcr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) → tb ++ [1] = ts)
    (hreindex :
      (((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
        + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
        + ((v + hexOmega ^ 2 * du) - v) * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi)
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi tb
          + ((v + hexOmega * du) - v)
              * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (tb ++ [-1])
          + ((v + hexOmega ^ 2 * du) - v)
              * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (tb ++ [1])) :
    HexSawClassification region a h0 v du where
  pairs := ∅
  pairBase := fun _ => []
  pairLq := fun _ => []
  pairLr := fun _ => []
  pairLq_sum := by simp
  pairLr_sum := by simp
  pairLen := by simp
  pairQ_valid := by simp
  pairR_valid := by simp
  pairQ_passes_p := by simp
  pairQ_passes_r := by simp
  pairR_passes_p := by simp
  pairR_passes_q := by simp
  triplets := {0}
  tripBase := fun _ => tb
  tripP_valid := fun _ _ => hp
  tripQ_valid := fun _ _ => hq
  tripR_valid := fun _ _ => hr
  tripQ_not_passes_r := fun _ _ => hQr
  tripR_not_passes_q := fun _ _ => hRq
  tripBase_inj := by
    rintro ⟨T1, hT1⟩ ⟨T2, hT2⟩ _
    simp only [Finset.mem_singleton] at hT1 hT2
    subst hT1; subst hT2; rfl
  pairQ_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp)
  pairR_inj := by rintro ⟨P1, hP1⟩; exact absurd hP1 (by simp)
  classify_p := fun ts hts hend => ⟨0, by simp, hcp ts hts hend⟩
  classify_q := fun ts hts hend => Or.inl ⟨0, by simp, hcq ts hts hend⟩
  classify_r := fun ts hts hend => Or.inl ⟨0, by simp, hcr ts hts hend⟩
  reindex := by
    rw [hreindex]
    rw [Finset.sum_empty, Finset.sum_singleton]
    ring


end StatMech.Universality
