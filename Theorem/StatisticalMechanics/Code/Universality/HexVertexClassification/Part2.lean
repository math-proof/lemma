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
import Def.StatisticalMechanics.Code.Universality.HexVertexClassification


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


namespace HexSawClassification

variable (C : HexSawClassification region a h0 v du)


@[simp] theorem toEnum_pairs : C.toEnum.pairs = C.pairs := rfl

@[simp] theorem toEnum_triplets : C.toEnum.triplets = C.triplets := rfl

@[simp] theorem toEnum_pairBase : C.toEnum.pairBase = C.pairBase := rfl

@[simp] theorem toEnum_pairLq : C.toEnum.pairLq = C.pairLq := rfl

@[simp] theorem toEnum_pairLr : C.toEnum.pairLr = C.pairLr := rfl

@[simp] theorem toEnum_tripBase : C.toEnum.tripBase = C.tripBase := rfl

end HexSawClassification


theorem hexClass_separated (C : HexSawClassification region a h0 v du) :
    HexVertexSeparated C.toEnum where
  pairQ_count_three := by
    intro P hP
    simp only [HexSawClassification.toEnum_pairBase, HexSawClassification.toEnum_pairLq]
    have hPmem : P ∈ C.pairs := by simpa using hP
    refine hexClass_specialMidCount_three_of_passes _ ?_ ?_ ?_
    · exact C.pairQ_passes_p P hPmem
    · exact hexClass_endsAt_passesThrough _ _ (C.pairQ_valid P hPmem).2.2
    · exact C.pairQ_passes_r P hPmem
  pairR_count_three := by
    intro P hP
    simp only [HexSawClassification.toEnum_pairBase, HexSawClassification.toEnum_pairLr]
    have hPmem : P ∈ C.pairs := by simpa using hP
    refine hexClass_specialMidCount_three_of_passes _ ?_ ?_ ?_
    · exact C.pairR_passes_p P hPmem
    · exact C.pairR_passes_q P hPmem
    · exact hexClass_endsAt_passesThrough _ _ (C.pairR_valid P hPmem).2.2
  tripQ_not_passes_r := by
    intro T hT
    simp only [HexSawClassification.toEnum_tripBase]
    exact C.tripQ_not_passes_r T (by simpa using hT)
  tripR_not_passes_q := by
    intro T hT
    simp only [HexSawClassification.toEnum_tripBase]
    exact C.tripR_not_passes_q T (by simpa using hT)


theorem hexClass_complete (C : HexSawClassification region a h0 v du) :
    HexVertexComplete C.toEnum where
  complete_p := by
    intro ts hts hp
    obtain ⟨T, hT, hbase⟩ := C.classify_p ts hts hp
    exact ⟨T, by simpa using hT, hbase⟩
  complete_q := by
    intro ts hts hq
    rcases C.classify_q ts hts hq with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
    · exact Or.inl ⟨T, by simpa using hT, hext⟩
    · exact Or.inr ⟨P, by simpa using hP, hwalk⟩
  complete_r := by
    intro ts hts hr
    rcases C.classify_r ts hts hr with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
    · exact Or.inl ⟨T, by simpa using hT, hext⟩
    · exact Or.inr ⟨P, by simpa using hP, hwalk⟩


theorem hexClass_vertex_relation (C : HexSawClassification region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  relation_of_complete C.toEnum hdu hp hq hr
    C.tripBase_inj C.pairQ_inj C.pairR_inj
    (hexSep_hqcross C.toEnum (hexClass_separated C))
    (hexSep_hrcross C.toEnum (hexClass_separated C))
    (hexClass_complete C)


end StatMech.Universality
