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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part25


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFreeEndpoint_lt_of_avoids
    (start level : Int) (bs : List Bool) (hstart : start < level)
    (havoid : forall k, k <= bs.length ->
      lineFreeEndpoint start (bs.take k) ≠ level) :
    lineFreeEndpoint start bs < level := by
  induction bs generalizing start with
  | nil => simpa [lineFreeEndpoint] using hstart
  | cons b bs ih =>
      let next := start + if b then 1 else -1
      have hnextLe : next <= level := by
        dsimp [next]
        cases b <;> simp <;> omega
      have hnextNe : next ≠ level := by
        have h := havoid 1 (by simp)
        simpa [lineFreeEndpoint, next] using h
      have htail : forall k, k <= bs.length ->
          lineFreeEndpoint next (bs.take k) ≠ level := by
        intro k hk
        have h := havoid (k + 1) (by simp; omega)
        simpa [lineFreeEndpoint, next, List.take_succ_cons] using h
      exact ih next (lt_of_le_of_ne hnextLe hnextNe) htail

theorem exists_sourceNoHitHorizontalCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    exists z : IsingEndpointFarEscapeWitnessFamily level t
        (p.2.1 : Int) (q.2.1 : Int),
      endpointFarEscapeValue level t (p.2.1 : Int) (q.2.1 : Int) z = w.1 := by
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    left
    exact hqLeft
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1 w.2.2 with
    ⟨k, hkT, hkOutput, hkMinimal⟩
  have hlevelPos : 0 < level := by
    have hpNonneg : 0 <= (isingLeapfrogBoxInt p).1 := by
      unfold isingLeapfrogBoxInt
      dsimp
      exact_mod_cast Nat.zero_le p.1.1
    omega
  have hstartX : ((level - 1 : Nat) : Int) =
      (isingLeapfrogBoxInt p).1 := by
    rw [Nat.cast_sub hlevelPos]
    norm_num
    omega
  have hcoord (l : Nat) (hl : l <= k) :=
    choiceRun_take_coordinates_eq_lineFree R t k p w.1 hkT hkMinimal l hl
  let xbits := (w.1.1.take k).map Prod.fst
  let ybits := (w.1.1.take k).map Prod.snd
  let tail := w.1.1.drop k
  have hxlen : xbits.length = k := by
    dsimp [xbits]
    simp [w.1.2, hkT]
  have hylen : ybits.length = k := by
    dsimp [ybits]
    simp [w.1.2, hkT]
  have htail : tail.length = t - k := by
    dsimp [tail]
    rw [List.length_drop, w.1.2]
  have hxTake (l : Nat) (hl : l <= k) :
      xbits.take l = (w.1.1.take l).map Prod.fst := by
    dsimp [xbits]
    rw [← List.map_take, List.take_take, Nat.min_eq_left hl]
  have hxInterior (l : Nat) (hl : l < k) :
      0 < lineFreeEndpoint ((level - 1 : Nat) : Int) (xbits.take l) /\
        lineFreeEndpoint ((level - 1 : Nat) : Int) (xbits.take l) < level := by
    have hc := (hcoord l hl.le).1
    have hnot := hkMinimal l hl
    rw [hxTake l hl.le]
    rw [hstartX, ← hc]
    have hpos : 0 < (isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 := by
      have hne : (isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 ≠ 0 := by
        intro heq
        apply hnot
        unfold isingLeapfrogBoxBoundary
        left
        exact heq
      omega
    have hltFree : lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.take l).map Prod.fst) < level := by
      apply lineFreeEndpoint_lt_of_avoids
      · omega
      · intro r hr
        have hrl : r <= l := by
          rw [List.length_map, List.length_take, w.1.2] at hr
          omega
        have hav := w.2.1 r (hrl.trans (hl.le.trans hkT))
        simpa [← List.map_take, List.take_take, Nat.min_eq_left hrl] using hav
    have hlt : ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) <
        level := by rw [hc]; exact hltFree
    exact ⟨by exact_mod_cast hpos, hlt⟩
  have hxFree (l : Nat) (hl : l <= k) :
      ((isingLineChoiceRun level ⟨level - 1, by omega⟩
        (xbits.take l)).1 : Int) =
      lineFreeEndpoint ((level - 1 : Nat) : Int) (xbits.take l) := by
    apply lineChoiceRun_val_eq_lineFreeEndpoint
    intro r hr
    have hrl : r < l := by rw [List.length_take, hxlen] at hr; omega
    have hi := hxInterior r (hrl.trans_le hl)
    have ht : (xbits.take l).take r = xbits.take r := by
      simp [List.take_take, Nat.min_eq_left hrl.le]
    rw [ht]
    exact ⟨ne_of_gt hi.1, ne_of_lt hi.2⟩
  have hxEnd : lineFreeEndpoint ((level - 1 : Nat) : Int) xbits = 0 := by
    have hc := (hcoord k le_rfl).1
    rw [hkOutput] at hc
    have htake : xbits.take k = xbits := by simpa [hxlen] using List.take_all xbits
    have hxEq := hxTake k le_rfl
    rw [htake] at hxEq
    rw [hstartX, hxEq, ← hc]
    exact_mod_cast hqLeft
  let xfar : IsingLineFarFirstBoundaryFamily level k := ⟨xbits, hxlen, by
    apply Fin.ext
    have hrun := hxFree k le_rfl
    have ht : xbits.take k = xbits := by simpa [hxlen] using List.take_all xbits
    rw [ht] at hrun
    change (isingLineChoiceRun level ⟨level - 1, by omega⟩ xbits).1 = 0
    exact_mod_cast hrun.trans hxEnd, by
      intro l hl
      have hi := hxInterior l hl
      have hrun := hxFree l hl.le
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb <;> exact (by omega)⟩
  have hyEnd : lineFreeEndpoint (p.2.1 : Int) ybits = q.2.1 := by
    have hc := (hcoord k le_rfl).2
    rw [hkOutput] at hc
    exact hc.symm
  let ypref : VerticalChoicePathFamily k (p.2.1 : Int) (q.2.1 : Int) :=
    ⟨ybits, hylen, hyEnd⟩
  let z : IsingEndpointFarEscapeWitnessFamily level t
      (p.2.1 : Int) (q.2.1 : Int) :=
    ⟨⟨k, by omega⟩, xfar, ypref, ⟨tail, htail⟩⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  dsimp [endpointFarEscapeValue, z, xfar, ypref, xbits, ybits, tail]
  rw [prodBits_zip_self_endpointFailure, List.take_append_drop]

end
end StatMech.Universality
