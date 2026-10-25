/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part7


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexPBase_valid (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (n : ℕ)
    (hn : n ∈ hexPBaseIndices R a h0 v du hdu) :
    (ofTurns a h0 (hexDecodedTurns n)).IsLegalSAW ∧
      (ofTurns a h0 (hexDecodedTurns n)).StaysIn R.inRegion ∧
      (ofTurns a h0 (hexDecodedTurns n)).EndsAt (v + du) := by
  rw [hexPBaseIndices, Finset.mem_image] at hn
  obtain ⟨ts, hts, rfl⟩ := hn
  have hparts :
      ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧
        (ofTurns a h0 ts).EndsAt (v + du) := by
    simpa [hexPBaseTurns] using hts
  have hsupp := (R.mem_supportFinset hdu ts).mp hparts.1
  have hvalid := R.support_isLegalSAW_staysIn hdu ts hsupp
  simpa using ⟨hvalid.1, hvalid.2, hparts.2⟩


theorem hexPBase_injective (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) :
    ∀ n₁ n₂ : hexPBaseIndices R a h0 v du hdu,
      hexDecodedTurns n₁ = hexDecodedTurns n₂ → n₁ = n₂ := by
  rintro ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ heq
  rw [hexPBaseIndices, Finset.mem_image] at hn₁ hn₂
  obtain ⟨ts₁, _, rfl⟩ := hn₁
  obtain ⟨ts₂, _, rfl⟩ := hn₂
  simp only [hexDecodedTurns_encode] at heq
  subst ts₂
  rfl


theorem hexPBase_classify (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ n : ℕ, n ∈ hexPBaseIndices R a h0 v du hdu ∧
        hexDecodedTurns n = ts := by
  intro ts hts hend
  refine ⟨Encodable.encode ts, ?_, hexDecodedTurns_encode ts⟩
  rw [hexPBaseIndices, Finset.mem_image]
  refine ⟨ts, ?_, rfl⟩
  simp only [hexPBaseTurns, Finset.mem_filter]
  exact ⟨(R.mem_supportFinset hdu ts).mpr hts, hend⟩


theorem no_fixedP_classification_of_nil_at_q
    (hsupp : ([] : List ℤ) ∈
      Function.support (combinedSummand region a h0 v du))
    (hend : (ofTurns a h0 ([] : List ℤ)).EndsAt
      (v + hexOmega * du)) :
    ¬ Nonempty (HexSawClassification region a h0 v du) := by
  rintro ⟨C⟩
  rcases C.classify_q [] hsupp hend with
    ⟨T, hT, hwalk⟩ | ⟨P, hP, hwalk⟩
  · have hlen := congrArg List.length hwalk
    simp at hlen
  · have hnil : C.pairLq P = [] := by
      have hlen := congrArg List.length hwalk
      simp only [List.length_append, List.length_nil] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hsum := C.pairLq_sum P hP
    rw [hnil] at hsum
    norm_num at hsum

end
end StatMech.Universality
