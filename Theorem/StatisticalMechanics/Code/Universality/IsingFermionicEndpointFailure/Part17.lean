/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part20


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem exists_mirrorOnlyOrderedCover
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    exists z : IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int),
      orderedFarEndpointValue (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int) z = w.1 /\
      forall hhalf : R <= 2 * level,
        exists zh : IsingOrderedFarHorizontalEndpointFamily (R - level) R t
            ⟨2 * level - R, by omega⟩ q.1
            (p.2.1 : Int) (q.2.1 : Int),
          orderedFarHorizontalEndpointValue (R - level) R t
            ⟨2 * level - R, by omega⟩ q.1
            (p.2.1 : Int) (q.2.1 : Int) zh = w.1 := by
  rcases mirrorOnly_ordered_boundary_marks R level t p p' q hstart hmirror hq w with
    ⟨split, j, k, hsplit, hjk, hkT, hjRight, hjSource, hjBetween,
      hjMirrorMinimal, hkOutput, hkMinimal⟩
  have hlevelLtR : level < R := by
    have hx := congrArg Prod.fst hmirror
    change (p'.1.1 : Int) = 2 * (level : Int) - (p.1.1 : Int) at hx
    have hp'Le : p'.1.1 <= R := by omega
    have hpX : (p.1.1 : Int) + 1 = level := hstart
    exact_mod_cast (show level < R by omega)
  have hcoord (l : Nat) (hl : l <= k) :=
    choiceRun_take_coordinates_eq_lineFree R t k p w.1 hkT hkMinimal l hl
  let xbits := (w.1.1.take j).map Prod.fst
  let ybits := (w.1.1.take k).map Prod.snd
  let midbits := ((w.1.1.drop j).take (k - j)).map Prod.fst
  let tail := w.1.1.drop k
  have hxlen : xbits.length = j := by
    dsimp [xbits]
    simp [w.1.2]
    omega
  have hylen : ybits.length = k := by
    dsimp [ybits]
    simp [w.1.2, hkT]
  have hmidlen : midbits.length = k - j := by
    dsimp [midbits]
    rw [List.length_map, List.length_take, List.length_drop, w.1.2]
    omega
  have htailLen : tail.length = t - k := by
    dsimp [tail]
    rw [List.length_drop, w.1.2]
  have hxTake (l : Nat) (hl : l <= j) :
      xbits.take l = (w.1.1.take l).map Prod.fst := by
    dsimp [xbits]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
  have hyTake (l : Nat) (hl : l <= k) :
      ybits.take l = (w.1.1.take l).map Prod.snd := by
    dsimp [ybits]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
  have hlineTranslate (l : Nat) (hl : l <= j) :
      lineFreeEndpoint (((R - level) - 1 : Nat) : Int) (xbits.take l) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take l).map Prod.fst) +
          ((R : Int) - 2 * level) := by
    have htr := lineFreeEndpoint_translate (xbits.take l)
      (isingLeapfrogBoxInt p).1 (((R - level) - 1 : Nat) : Int)
    rw [hxTake l hl] at htr
    rw [hxTake l hl]
    rw [htr]
    have hcastR : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    have hcastPos : ((((R - level) - 1 : Nat) : Int)) =
        (R : Int) - level - 1 := by
      rw [Nat.cast_sub (show 1 <= R - level by omega), hcastR]
      norm_num
    rw [hcastPos]
    omega
  have hxInterior (l : Nat) (hl : l < j) :
      0 < lineFreeEndpoint (((R - level) - 1 : Nat) : Int)
          (xbits.take l) /\
        lineFreeEndpoint (((R - level) - 1 : Nat) : Int)
          (xbits.take l) < (R - level : Nat) := by
    have hc := hcoord l (hl.le.trans hjk.le)
    have hb := hjBetween l hl
    have htr := hlineTranslate l hl.le
    rw [← hc.1] at htr
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    exact ⟨by omega, by rw [hcast]; omega⟩
  have hxFree (l : Nat) (hl : l <= j) :
      ((isingLineChoiceRun (R - level)
        ⟨(R - level) - 1, by omega⟩ (xbits.take l)).1 : Int) =
        lineFreeEndpoint (((R - level) - 1 : Nat) : Int)
          (xbits.take l) := by
    apply lineChoiceRun_val_eq_lineFreeEndpoint
    intro r hr
    have hrl : r < l := by
      rw [List.length_take, hxlen] at hr
      omega
    have hi := hxInterior r (hrl.trans_le hl)
    have htake : (xbits.take l).take r = xbits.take r := by
      simp [List.take_take, Nat.min_eq_left hrl.le]
    rw [htake]
    exact ⟨ne_of_gt hi.1, ne_of_lt hi.2⟩
  have hxEnd : lineFreeEndpoint (((R - level) - 1 : Nat) : Int) xbits = 0 := by
    have htr := hlineTranslate j le_rfl
    have htakeAll : xbits.take j = xbits := by
      simpa [hxlen] using List.take_all xbits
    rw [htakeAll] at htr
    have hc := (hcoord j hjk.le).1
    rw [← hc, hjSource] at htr
    linarith
  let xfar : IsingLineFarFirstBoundaryFamily (R - level) j := ⟨xbits,
    hxlen, by
      apply Fin.ext
      have hrun := hxFree j le_rfl
      have htakeAll : xbits.take j = xbits := by
        simpa [hxlen] using List.take_all xbits
      rw [htakeAll] at hrun
      change (isingLineChoiceRun (R - level)
        ⟨(R - level) - 1, by omega⟩ xbits).1 = 0
      exact_mod_cast hrun.trans hxEnd,
    by
      intro l hl
      have hi := hxInterior l hl
      have hrun := hxFree l hl.le
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb <;> exact (by omega)⟩
  have hyInterior (l : Nat) (hl : l < k) :
      lineFreeEndpoint (isingLeapfrogBoxInt p).2 (ybits.take l) ≠ 0 /\
        lineFreeEndpoint (isingLeapfrogBoxInt p).2 (ybits.take l) ≠ R := by
    have hc := hcoord l hl.le
    have hnot := hkMinimal l hl
    rw [hyTake l hl.le, ← hc.2]
    constructor
    · intro hzero
      apply hnot
      unfold isingLeapfrogBoxBoundary
      right; right; left
      exact_mod_cast hzero
    · intro hright
      apply hnot
      unfold isingLeapfrogBoxBoundary
      right; right; right
      omega
  have hyFree (l : Nat) (hl : l <= k) :
      ((isingLineChoiceRun R p.2 (ybits.take l)).1 : Int) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).2 (ybits.take l) := by
    apply lineChoiceRun_val_eq_lineFreeEndpoint
    intro r hr
    have hrl : r < l := by
      rw [List.length_take, hylen] at hr
      omega
    have hi := hyInterior r (hrl.trans_le hl)
    have htake : (ybits.take l).take r = ybits.take r := by
      simp [List.take_take, Nat.min_eq_left hrl.le]
    simpa [htake] using hi
  have hyEnd : lineFreeEndpoint (isingLeapfrogBoxInt p).2 ybits = q.2.1 := by
    have hc := (hcoord k le_rfl).2
    rw [hkOutput] at hc
    have htakeAll : ybits.take k = ybits := by
      simpa [hylen] using List.take_all ybits
    have hyEq := hyTake k le_rfl
    rw [htakeAll] at hyEq
    rw [← hyEq] at hc
    exact hc.symm
  let yfirst : IsingLineFirstEndpointFamily R k p.2 q.2 := ⟨ybits,
    hylen, by
      apply Fin.ext
      have hrun := hyFree k le_rfl
      have htakeAll : ybits.take k = ybits := by
        simpa [hylen] using List.take_all ybits
      rw [htakeAll] at hrun
      change (isingLineChoiceRun R p.2 ybits).1 = q.2.1
      exact_mod_cast hrun.trans hyEnd,
    by
      intro l hl
      have hi := hyInterior l hl
      have hrun := hyFree l hl.le
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb <;> exact (by omega)⟩
  have hprefixDecomp :
      (w.1.1.take j).map Prod.fst ++ midbits =
        (w.1.1.take k).map Prod.fst := by
    dsimp [midbits]
    rw [← List.map_append, ← List.take_add]
    congr 2
    omega
  have hmidEnd : lineFreeEndpoint (2 * (level : Int) - R) midbits = q.1 := by
    have hjc := (hcoord j hjk.le).1
    have hkc := (hcoord k le_rfl).1
    rw [hjSource] at hjc
    rw [hkOutput] at hkc
    calc
      lineFreeEndpoint (2 * (level : Int) - R) midbits =
          lineFreeEndpoint
            (lineFreeEndpoint (isingLeapfrogBoxInt p).1
              ((w.1.1.take j).map Prod.fst)) midbits := by rw [← hjc]
      _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
          ((w.1.1.take j).map Prod.fst ++ midbits) :=
        (lineFreeEndpoint_append_endpointFailure ..).symm
      _ = _ := by rw [hprefixDecomp, ← hkc]
  let xmid : VerticalChoicePathFamily (k - j)
      (2 * (level : Int) - R) (q.1 : Int) := ⟨midbits, hmidlen, hmidEnd⟩
  let z : IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
      (2 * (level : Int) - R) (q.1 : Int) :=
    ⟨⟨k, by omega⟩, ⟨⟨j, hjk⟩, xfar, yfirst, xmid, ⟨tail, htailLen⟩⟩⟩
  have hxFull :
      (w.1.1.take j).map Prod.fst ++
          ((w.1.1.drop j).take (k - j)).map Prod.fst ++
          (w.1.1.drop k).map Prod.fst = w.1.1.map Prod.fst := by
    rw [hprefixDecomp]
    rw [← List.map_append, List.take_append_drop]
  have hyFull :
      (w.1.1.take k).map Prod.snd ++ (w.1.1.drop k).map Prod.snd =
        w.1.1.map Prod.snd := by
    rw [← List.map_append, List.take_append_drop]
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    dsimp [orderedFarEndpointValue, z, xfar, yfirst, xmid, tail,
      xbits, ybits, midbits]
    rw [hxFull, hyFull, prodBits_zip_self_endpointFailure]
  · intro hhalf
    let mark : IsingLineBox R := ⟨2 * level - R, by omega⟩
    have hmarkCast : (mark.1 : Int) = 2 * (level : Int) - R := by
      dsimp [mark]
      rw [Nat.cast_sub hhalf]
      push_cast
      ring
    have hmidTake (l : Nat) (hl : l <= k - j) :
        midbits.take l = ((w.1.1.drop j).take l).map Prod.fst := by
      dsimp [midbits]
      rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
    have hprefixAt (l : Nat) (hl : l <= k - j) :
        (w.1.1.take j).map Prod.fst ++
            ((w.1.1.drop j).take l).map Prod.fst =
          (w.1.1.take (j + l)).map Prod.fst := by
      rw [← List.map_append, ← List.take_add]
    have hsegment (l : Nat) (hl : l <= k - j) :
        lineFreeEndpoint (mark.1 : Int) (midbits.take l) =
          lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take (j + l)).map Prod.fst) := by
      have hjc := (hcoord j hjk.le).1
      rw [hjSource] at hjc
      calc
        lineFreeEndpoint (mark.1 : Int) (midbits.take l) =
            lineFreeEndpoint
              (lineFreeEndpoint (isingLeapfrogBoxInt p).1
                ((w.1.1.take j).map Prod.fst)) (midbits.take l) := by
          rw [hmarkCast, hjc]
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.take j).map Prod.fst ++ midbits.take l) :=
          (lineFreeEndpoint_append_endpointFailure ..).symm
        _ = _ := by rw [hmidTake l hl, hprefixAt l hl]
    have hmidInterior (l : Nat) (hl : l < k - j) :
        lineFreeEndpoint (mark.1 : Int) (midbits.take l) ≠ 0 /\
          lineFreeEndpoint (mark.1 : Int) (midbits.take l) ≠ R := by
      have hjl : j + l < k := by omega
      have hc := hcoord (j + l) hjl.le
      have hnot := hkMinimal (j + l) hjl
      rw [hsegment l hl.le, ← hc.1]
      constructor
      · intro hzero
        apply hnot
        unfold isingLeapfrogBoxBoundary
        left
        exact_mod_cast hzero
      · intro hright
        apply hnot
        unfold isingLeapfrogBoxBoundary
        right; left
        omega
    have hmidFree (l : Nat) (hl : l <= k - j) :
        ((isingLineChoiceRun R mark (midbits.take l)).1 : Int) =
          lineFreeEndpoint (mark.1 : Int) (midbits.take l) := by
      apply lineChoiceRun_val_eq_lineFreeEndpoint
      intro r hr
      have hrl : r < l := by
        rw [List.length_take, hmidlen] at hr
        omega
      have hi := hmidInterior r (hrl.trans_le hl)
      have htake : (midbits.take l).take r = midbits.take r := by
        simp [List.take_take, Nat.min_eq_left hrl.le]
      simpa [htake] using hi
    let xfirst : IsingLineFirstEndpointFamily R (k - j) mark q.1 :=
      ⟨midbits, hmidlen, by
        apply Fin.ext
        have hrun := hmidFree (k - j) le_rfl
        have htakeAll : midbits.take (k - j) = midbits := by
          simpa [hmidlen] using List.take_all midbits
        rw [htakeAll] at hrun
        change (isingLineChoiceRun R mark midbits).1 = q.1.1
        have hint : ((isingLineChoiceRun R mark midbits).1 : Int) =
            (q.1.1 : Int) :=
          hrun.trans (by simpa [hmarkCast] using hmidEnd)
        exact Int.ofNat_inj.mp hint,
      by
        intro l hl
        have hi := hmidInterior l hl
        have hrun := hmidFree l hl.le
        intro hb
        unfold isingLineBoxBoundary at hb
        rcases hb with hb | hb <;> exact (by omega)⟩
    let yfree : VerticalChoicePathFamily k (p.2.1 : Int) (q.2.1 : Int) :=
      ⟨ybits, hylen, hyEnd⟩
    let zh : IsingOrderedFarHorizontalEndpointFamily (R - level) R t
        mark q.1 (p.2.1 : Int) (q.2.1 : Int) :=
      ⟨⟨k, by omega⟩, ⟨⟨j, hjk⟩, xfar, xfirst, yfree,
        ⟨tail, htailLen⟩⟩⟩
    refine ⟨zh, ?_⟩
    apply Subtype.ext
    dsimp [orderedFarHorizontalEndpointValue, zh, xfar, xfirst, yfree,
      tail, xbits, ybits, midbits]
    rw [hxFull, hyFull, prodBits_zip_self_endpointFailure]

end
end StatMech.Universality
