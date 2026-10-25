/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part6


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexKOneBase_valid (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) (n : ℕ)
    (hn : n ∈ hexKOneBaseIndices R a h0 v du hdu j) :
    (ofTurns a h0 (hexDecodedTurns n)).IsLegalSAW ∧
      (ofTurns a h0 (hexDecodedTurns n)).StaysIn R.inRegion ∧
      (ofTurns a h0 (hexDecodedTurns n)).EndsAt (labelMid v du j) ∧
      specialMidCount a h0 v du (hexDecodedTurns n) = 1 := by
  rw [hexKOneBaseIndices, Finset.mem_image] at hn
  obtain ⟨ts, hts, rfl⟩ := hn
  have hparts := (mem_hexKOneBaseTurns R a h0 v du hdu j ts).mp hts
  have hsupp := (R.mem_supportFinset hdu ts).mp hparts.1
  have hvalid := R.support_isLegalSAW_staysIn hdu ts hsupp
  simpa using ⟨hvalid.1, hvalid.2, hparts.2.2, hparts.2.1⟩


theorem hexKOneBase_injective (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) :
    ∀ n₁ n₂ : hexKOneBaseIndices R a h0 v du hdu j,
      hexDecodedTurns n₁ = hexDecodedTurns n₂ → n₁ = n₂ := by
  rintro ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ heq
  rw [hexKOneBaseIndices, Finset.mem_image] at hn₁ hn₂
  obtain ⟨ts₁, _, rfl⟩ := hn₁
  obtain ⟨ts₂, _, rfl⟩ := hn₂
  simp only [hexDecodedTurns_encode] at heq
  subst ts₂
  rfl


theorem hexKOneBase_classify (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      specialMidCount a h0 v du ts = 1 →
      (ofTurns a h0 ts).EndsAt (labelMid v du j) →
      ∃ n : ℕ, n ∈ hexKOneBaseIndices R a h0 v du hdu j ∧
        hexDecodedTurns n = ts := by
  intro ts hts hcount hend
  refine ⟨Encodable.encode ts, ?_, hexDecodedTurns_encode ts⟩
  rw [hexKOneBaseIndices, Finset.mem_image]
  refine ⟨ts, ?_, rfl⟩
  exact (mem_hexKOneBaseTurns R a h0 v du hdu j ts).mpr
    ⟨(R.mem_supportFinset hdu ts).mpr hts, hcount, hend⟩


theorem hexVisitClass_one_eq_cyclicBases (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    hexVisitClassFinset R a h0 v du hdu 1 =
      hexKOneBaseTurns R a h0 v du hdu 0 ∪
        hexKOneBaseTurns R a h0 v du hdu 1 ∪
        hexKOneBaseTurns R a h0 v du hdu 2 := by
  ext ts
  constructor
  · intro hts
    have hparts :=
      (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mp hts
    have hsupp := (R.mem_supportFinset hdu ts).mp hparts.1
    rcases support_endsAt_threeMid ts hsupp with hp | hq | hr
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact (mem_hexKOneBaseTurns R a h0 v du hdu 0 ts).mpr
        ⟨hparts.1, hparts.2, by simpa [labelMid] using hp⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact (mem_hexKOneBaseTurns R a h0 v du hdu 1 ts).mpr
        ⟨hparts.1, hparts.2, by simpa [labelMid] using hq⟩
    · apply Finset.mem_union_right
      exact (mem_hexKOneBaseTurns R a h0 v du hdu 2 ts).mpr
        ⟨hparts.1, hparts.2, by simpa [labelMid] using hr⟩
  · intro hts
    rcases Finset.mem_union.mp hts with h01 | hb2
    · rcases Finset.mem_union.mp h01 with hb0 | hb1
      · have h := (mem_hexKOneBaseTurns R a h0 v du hdu 0 ts).mp hb0
        exact (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mpr
          ⟨h.1, h.2.1⟩
      · have h := (mem_hexKOneBaseTurns R a h0 v du hdu 1 ts).mp hb1
        exact (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mpr
          ⟨h.1, h.2.1⟩
    · have h := (mem_hexKOneBaseTurns R a h0 v du hdu 2 ts).mp hb2
      exact (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mpr
        ⟨h.1, h.2.1⟩


theorem hexKOneBaseTurns_disjoint (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    {j k : Fin 3} (hjk : j ≠ k) :
    Disjoint (hexKOneBaseTurns R a h0 v du hdu j)
      (hexKOneBaseTurns R a h0 v du hdu k) := by
  rw [Finset.disjoint_left]
  intro ts hj hk
  have hj' := (mem_hexKOneBaseTurns R a h0 v du hdu j ts).mp hj
  have hk' := (mem_hexKOneBaseTurns R a h0 v du hdu k ts).mp hk
  apply hjk
  apply labelMid_injective hdu
  unfold HexWalk.EndsAt at hj' hk'
  exact hj'.2.2.symm.trans hk'.2.2


end
end StatMech.Universality
