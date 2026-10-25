/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean -/

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
import Structure.StatisticalMechanics.Code.Universality.HexVertexSeparation


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexSep_hqcross (E : HexVertexEnumeration region a h0 v du)
    (hS : HexVertexSeparated E) :
    ∀ (P : E.pairs) (T : E.triplets),
      E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1] := by
  rintro ⟨P, hP⟩ ⟨T, hT⟩ heq
  have h1 : PassesThrough a h0 (E.pairBase P ++ E.pairLq P) (v + hexOmega ^ 2 * du) :=
    hexSep_passesThrough_r_of_count_three _ (hS.pairQ_count_three P hP)
  rw [heq] at h1
  exact hS.tripQ_not_passes_r T hT h1


theorem hexSep_hrcross (E : HexVertexEnumeration region a h0 v du)
    (hS : HexVertexSeparated E) :
    ∀ (P : E.pairs) (T : E.triplets),
      E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1] := by
  rintro ⟨P, hP⟩ ⟨T, hT⟩ heq
  have h1 : PassesThrough a h0 (E.pairBase P ++ E.pairLr P) (v + hexOmega * du) :=
    hexSep_passesThrough_q_of_count_three _ (hS.pairR_count_three P hP)
  rw [heq] at h1
  exact hS.tripR_not_passes_q T hT h1


theorem hexSep_hinj (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hS : HexVertexSeparated E) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_general E hdu htinj hqinj hrinj (hexSep_hqcross E hS) (hexSep_hrcross E hS)


theorem hexSep_relation (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hS : HexVertexSeparated E)
    (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  HexVertexEnumeration.relation_of_bijection E hdu hp hq hr
    (hexSep_hinj E hdu htinj hqinj hrinj hS)
    (hsub_of_coverage E covp covq covr)


theorem hexSep_separated_empty (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (hzero : ∀ z, parafObservable (fun _ => False) a h0 z (5/8) hexChi = 0) :
    HexVertexSeparated (HexVertexEnumeration.empty (fun _ => False) a h0 v du hzero) where
  pairQ_count_three := by
    intro P hP; exact absurd hP (by simp [HexVertexEnumeration.empty])
  pairR_count_three := by
    intro P hP; exact absurd hP (by simp [HexVertexEnumeration.empty])
  tripQ_not_passes_r := by
    intro T hT; exact absurd hT (by simp [HexVertexEnumeration.empty])
  tripR_not_passes_q := by
    intro T hT; exact absurd hT (by simp [HexVertexEnumeration.empty])

end StatMech.Universality
