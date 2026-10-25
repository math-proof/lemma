/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


namespace HexFiniteRegion

variable (R : HexFiniteRegion)


variable {a : ℂ} {h0 : ℤ} {v du : ℂ}


@[simp]
theorem mem_supportFinset (hdu : du ≠ 0) (ts : List ℤ) :
    ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu
      ↔ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du) := by
  unfold supportFinset
  exact Set.Finite.mem_toFinset _


theorem classify_p_from_covering
    (triplets : Finset ℕ) (tripBase : ℕ → List ℤ)
    (covp : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts := by
  intro ts hts hp
  obtain ⟨T, hT, hbase⟩ := covp ts hts hp
  exact ⟨T, hT, hbase⟩


theorem classify_q_from_covering
    (pairs triplets : Finset ℕ) (pairBase pairLq tripBase : ℕ → List ℤ)
    (covq : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T ∈ triplets, tripBase T ++ [-1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts) := by
  intro ts hts hq
  rcases covq ts hts hq with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
  · exact Or.inl ⟨T, hT, hext⟩
  · exact Or.inr ⟨P, hP, hwalk⟩


theorem classify_r_from_covering
    (pairs triplets : Finset ℕ) (pairBase pairLr tripBase : ℕ → List ℤ)
    (covr : ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T ∈ triplets, tripBase T ++ [1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts) := by
  intro ts hts hr
  rcases covr ts hts hr with ⟨T, hT, hext⟩ | ⟨P, hP, hwalk⟩
  · exact Or.inl ⟨T, hT, hext⟩
  · exact Or.inr ⟨P, hP, hwalk⟩

end HexFiniteRegion
end StatMech.Universality
