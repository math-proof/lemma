/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexPairing_loopReverse_pairs (Lq : List ℤ) (hLqsum : Lq.sum = -4) :
    (loopReverse Lq).sum = 4 ∧ (loopReverse Lq).length = Lq.length
      ∧ loopReverse (loopReverse Lq) = Lq := by
  refine ⟨?_, loopReverse_length Lq, loopReverse_involutive Lq⟩
  rw [loopReverse_sum, hLqsum]; ring


theorem hexPairing_loopReverse_legal (Lq : List ℤ)
    (hLq : ∀ t ∈ Lq, t = 1 ∨ t = -1) :
    ∀ t ∈ loopReverse Lq, t = 1 ∨ t = -1 :=
  loopReverse_legal Lq hLq


theorem hexPairing_pair_walks_ne (base Lq : List ℤ) (hLqsum : Lq.sum = -4) :
    base ++ Lq ≠ base ++ loopReverse Lq := by
  intro h
  have hcancel : Lq = loopReverse Lq := List.append_cancel_left h
  have h1 : (loopReverse Lq).sum = -4 := by rw [← hcancel]; exact hLqsum
  have h2 : (loopReverse Lq).sum = 4 := by rw [loopReverse_sum, hLqsum]; ring
  rw [h1] at h2; norm_num at h2


theorem hexPairing_pair_involution (base Lq : List ℤ) (hLqsum : Lq.sum = -4) :
    loopReverse (loopReverse Lq) = Lq
      ∧ base ++ Lq ≠ base ++ loopReverse Lq
      ∧ (loopReverse Lq).sum = 4 ∧ (loopReverse Lq).length = Lq.length :=
  ⟨loopReverse_involutive Lq, hexPairing_pair_walks_ne base Lq hLqsum,
    (hexPairing_loopReverse_pairs Lq hLqsum).1, (hexPairing_loopReverse_pairs Lq hLqsum).2.1⟩

namespace HexFiniteRegion

variable (R : HexFiniteRegion)


theorem classify_p_of_supportFinset_covering (hdu : du ≠ 0)
    (triplets : Finset ℕ) (tripBase : ℕ → List ℤ)
    (covp : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + du) → ∃ T ∈ triplets, tripBase T = ts) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ T : ℕ, T ∈ triplets ∧ tripBase T = ts := by
  apply R.classify_p_from_covering triplets tripBase
  intro ts hts hp
  exact covp ts ((R.mem_supportFinset hdu ts).mpr hts) hp


theorem classify_q_of_supportFinset_covering (hdu : du ≠ 0)
    (pairs triplets : Finset ℕ) (pairBase pairLq tripBase : ℕ → List ℤ)
    (covq : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T ∈ triplets, tripBase T ++ [-1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLq P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [-1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLq P = ts) := by
  apply R.classify_q_from_covering pairs triplets pairBase pairLq tripBase
  intro ts hts hq
  exact covq ts ((R.mem_supportFinset hdu ts).mpr hts) hq


theorem classify_r_of_supportFinset_covering (hdu : du ≠ 0)
    (pairs triplets : Finset ℕ) (pairBase pairLr tripBase : ℕ → List ℤ)
    (covr : ∀ ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu,
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T ∈ triplets, tripBase T ++ [1] = ts)
        ∨ (∃ P ∈ pairs, pairBase P ++ pairLr P = ts)) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
      (∃ T : ℕ, T ∈ triplets ∧ tripBase T ++ [1] = ts)
        ∨ (∃ P : ℕ, P ∈ pairs ∧ pairBase P ++ pairLr P = ts) := by
  apply R.classify_r_from_covering pairs triplets pairBase pairLr tripBase
  intro ts hts hr
  exact covr ts ((R.mem_supportFinset hdu ts).mpr hts) hr

end HexFiniteRegion
end StatMech.Universality
