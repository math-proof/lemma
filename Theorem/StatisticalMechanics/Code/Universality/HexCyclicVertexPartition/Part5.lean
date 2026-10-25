/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


@[simp] theorem mem_hexVisitClassFinset (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) (k : ℕ)
    (ts : List ℤ) :
    ts ∈ hexVisitClassFinset R a h0 v du hdu k ↔
      ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧
        specialMidCount a h0 v du ts = k := by
  simp [hexVisitClassFinset]


theorem specialMidCount_le_three (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ) : specialMidCount a h0 v du ts ≤ 3 := by
  classical
  unfold specialMidCount
  split <;> split <;> split <;> omega


theorem support_specialMidCount_pos
    (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand region a h0 v du)) :
    0 < specialMidCount a h0 v du ts := by
  classical
  rcases support_endsAt_threeMid ts hts with hp | hq | hr
  · have hpass := hexClass_endsAt_passesThrough ts (v + du) hp
    unfold specialMidCount
    rw [if_pos hpass]
    split <;> split <;> omega
  · have hpass := hexClass_endsAt_passesThrough ts
      (v + hexOmega * du) hq
    unfold specialMidCount
    rw [if_pos hpass]
    split <;> split <;> omega
  · have hpass := hexClass_endsAt_passesThrough ts
      (v + hexOmega ^ 2 * du) hr
    unfold specialMidCount
    rw [if_pos hpass]
    split <;> split <;> omega


theorem support_specialMidCount_cases
    (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand region a h0 v du)) :
    specialMidCount a h0 v du ts = 1 ∨
      specialMidCount a h0 v du ts = 2 ∨
      specialMidCount a h0 v du ts = 3 := by
  have hlo := support_specialMidCount_pos ts hts
  have hhi := specialMidCount_le_three a h0 v du ts
  omega


theorem supportFinset_eq_visitClasses (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu =
      hexVisitClassFinset R a h0 v du hdu 1 ∪
        hexVisitClassFinset R a h0 v du hdu 2 ∪
        hexVisitClassFinset R a h0 v du hdu 3 := by
  ext ts
  constructor
  · intro hts
    have hsupp := (R.mem_supportFinset hdu ts).mp hts
    rcases support_specialMidCount_cases ts hsupp with h1 | h2 | h3
    · simp [mem_hexVisitClassFinset, hts, h1]
    · simp [mem_hexVisitClassFinset, hts, h2]
    · simp [mem_hexVisitClassFinset, hts, h3]
  · intro hts
    simp only [Finset.mem_union, mem_hexVisitClassFinset] at hts
    rcases hts with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h


theorem hexVisitClassFinset_disjoint (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (hexVisitClassFinset R a h0 v du hdu k)
      (hexVisitClassFinset R a h0 v du hdu l) := by
  rw [Finset.disjoint_left]
  intro ts hk hl
  have hk' := (mem_hexVisitClassFinset R a h0 v du hdu k ts).mp hk
  have hl' := (mem_hexVisitClassFinset R a h0 v du hdu l ts).mp hl
  exact hkl (hk'.2.symm.trans hl'.2)


end
end StatMech.Universality
