/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part11


namespace StatMech.Universality

open HexWalk


theorem hlha_prefix_reverse_away (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW)
    (hne : ts.take (hexW2_cutPos 0 ts) ≠ []) :
    HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ts.take (hexW2_cutPos 0 ts))).dir) := by
  obtain ⟨t, us, hp⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hd, _⟩ := hlha_prefix_side_hypotheses a h0 ts hsource hp
  simpa [hlha_cutState] using hd

theorem hlha_suffix_forward_away (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) {t : ℤ} {us : List ℤ}
    (hs : ts.drop (hexW2_cutPos 0 ts) = t :: us) :
    HLHAAwayDir ((hlha_cutState ts).dir.turn t) :=
  (hlha_suffix_side_hypotheses a h0 ts hsource hs).1

theorem hlha_augmentedPair_injective (a : ℂ) (h0 : ℤ)
    {xs ys : List ℤ}
    (hx : (ofTurns a h0 xs).IsLegalSAW)
    (hy : (ofTurns a h0 ys).IsLegalSAW)
    (heq : hlha_augmentedPair xs = hlha_augmentedPair ys) : xs = ys := by
  have hpreAug := congrArg Prod.fst heq
  have hsufAug := congrArg Prod.snd heq
  let px := xs.take (hexW2_cutPos 0 xs)
  let py := ys.take (hexW2_cutPos 0 ys)
  have hpxlegal : ∀ t ∈ px, t = 1 ∨ t = -1 := by
    intro t ht
    exact hx.1 t (List.mem_of_mem_take ht)
  have hpylegal : ∀ t ∈ py, t = 1 ∨ t = -1 := by
    intro t ht
    exact hy.1 t (List.mem_of_mem_take ht)
  have hpre : px = py := by
    apply hlha_reverseAugment_injective_of_away hpxlegal hpylegal
    · intro hne
      exact hlha_prefix_reverse_away a h0 xs hx hne
    · intro hne
      exact hlha_prefix_reverse_away a h0 ys hy hne
    · rw [← hlha_prefixAugment_eq_reverseAugment,
        ← hlha_prefixAugment_eq_reverseAugment]
      exact hpreAug
  have hcpx : (px.length = hexW2_cutPos 0 xs) := by
    simp [px, List.length_take_of_le (hexW2_cutPos_le 0 xs)]
  have hcpy : (py.length = hexW2_cutPos 0 ys) := by
    simp [py, List.length_take_of_le (hexW2_cutPos_le 0 ys)]
  have hcp : hexW2_cutPos 0 xs = hexW2_cutPos 0 ys := by
    rw [← hcpx, ← hcpy, hpre]
  let r := hlha_cutState xs
  have hr : hlha_cutState ys = r := by
    unfold hlha_cutState r
    exact congrArg (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base) hpre.symm
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit HexReturnCoord.zero
      HexReturnCoord.base px HexReturnCoord.base_isUnit hpxlegal
  let sx := xs.drop (hexW2_cutPos 0 xs)
  let sy := ys.drop (hexW2_cutPos 0 ys)
  have hsxlegal : ∀ t ∈ sx, t = 1 ∨ t = -1 := by
    intro t ht
    exact hx.1 t (List.mem_of_mem_drop ht)
  have hsylegal : ∀ t ∈ sy, t = 1 ∨ t = -1 := by
    intro t ht
    exact hy.1 t (List.mem_of_mem_drop ht)
  have hsuf : sx = sy := by
    apply hlha_forwardAugment_injective_of_away r.dir hrunit
      hsxlegal hsylegal
    · intro t us hs
      exact hlha_suffix_forward_away a h0 xs hx hs
    · intro t us hs
      have ha := hlha_suffix_forward_away a h0 ys hy hs
      rw [hr] at ha
      exact ha
    · calc
        hlha_forwardAugment r.dir sx = hlha_suffixAugment xs := by
          symm
          simpa [r, sx] using hlha_suffixAugment_eq_forwardAugment xs
        _ = hlha_suffixAugment ys := by
          simpa [hlha_augmentedPair] using hsufAug
        _ = hlha_forwardAugment r.dir sy := by
          rw [hlha_suffixAugment_eq_forwardAugment, hr]
  have hxs : xs = px ++ sx := by
    simpa [px, sx] using
      (List.take_append_drop (hexW2_cutPos 0 xs) xs).symm
  have hys : py ++ sy = ys := by
    simpa [py, sy] using List.take_append_drop (hexW2_cutPos 0 ys) ys
  exact hxs.trans ((congrArg₂ List.append hpre hsuf).trans hys)


@[simp] theorem hlha_prefixAugment_cons_tail (ts : List ℤ) :
    (-1 : ℤ) :: (hlha_prefixAugment ts).tail = hlha_prefixAugment ts := by
  unfold hlha_prefixAugment hlha_prefixReverseData
  generalize ts.take (hexW2_cutPos 0 ts) = pre
  cases pre <;> simp [hlha_emptyAugment, hlha_augmentSide]


@[simp] theorem hlha_suffixAugment_cons_tail (ts : List ℤ) :
    (-1 : ℤ) :: (hlha_suffixAugment ts).tail = hlha_suffixAugment ts := by
  unfold hlha_suffixAugment
  generalize ts.drop (hexW2_cutPos 0 ts) = suf
  cases suf <;> simp [hlha_emptyAugment, hlha_augmentSide]


end StatMech.Universality
