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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part26


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceNoHitHorizontalCover_value
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    endpointFarEscapeValue level t (p.2.1 : Int) (q.2.1 : Int)
        (sourceNoHitHorizontalCover R level t p q hstart hqLeft w) = w.1 := by
  exact Classical.choose_spec
    (exists_sourceNoHitHorizontalCover R level t p q hstart hqLeft w)

theorem sourceNoHitHorizontalCover_injective
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    Function.Injective
      (sourceNoHitHorizontalCover R level t p q hstart hqLeft) := by
  intro a b hab
  apply Subtype.ext
  rw [← sourceNoHitHorizontalCover_value R level t p q hstart hqLeft a,
    ← sourceNoHitHorizontalCover_value R level t p q hstart hqLeft b,
    hab]

theorem isEmpty_sourceNoHitOutput_right
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevelR : level <= R)
    (hqRight : q.1.1 = R) :
    IsEmpty (IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) := by
  constructor
  intro w
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    right; left
    omega
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1 w.2.2 with
    ⟨k, hkT, hkOutput, hkMinimal⟩
  have hcoord := choiceRun_take_coordinates_eq_lineFree
    R t k p w.1 hkT hkMinimal k le_rfl
  have hbelow : lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.1.take k).map Prod.fst) < level := by
    apply lineFreeEndpoint_lt_of_avoids
    · omega
    · intro r hr
      have hrk : r <= k := by
        rw [List.length_map, List.length_take, w.1.2] at hr
        omega
      have hav := w.2.1 r (hrk.trans hkT)
      simpa [← List.map_take, List.take_take, Nat.min_eq_left hrk] using hav
  rw [← hcoord.1, hkOutput] at hbelow
  have : ((q.1.1 : Nat) : Int) = R := by exact_mod_cast hqRight
  omega

theorem sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le
    (R level rho : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hleft : rho <= level) (hlevelR : level <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    Nat.card (IsingSourceChoiceNoHitOutputAtFamily
        R (rho * rho) p q (level : Int)) /
        (4 : Real) ^ (rho * rho) <=
      468 / (rho : Real) ^ 2 := by
  rcases hqHorizontal with hqLeft | hqRight
  · have hcard := Nat.card_le_card_of_injective
        (sourceNoHitHorizontalCover R level (rho * rho) p q hstart hqLeft)
        (sourceNoHitHorizontalCover_injective R level (rho * rho)
          p q hstart hqLeft)
    calc
      Nat.card (IsingSourceChoiceNoHitOutputAtFamily
          R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <=
        Nat.card (IsingEndpointFarEscapeWitnessFamily level (rho * rho)
          (p.2.1 : Int) (q.2.1 : Int)) / (4 : Real) ^ (rho * rho) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ <= 468 / (rho : Real) ^ 2 :=
        endpointFarEscapeWitness_diffusive_weight_le rho level
          (p.2.1 : Int) (q.2.1 : Int) hρ hleft
  · letI := isEmpty_sourceNoHitOutput_right
      R level (rho * rho) p q hstart hlevelR hqRight
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    positivity

theorem exists_sourceNoHitVerticalCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R)
    (w : IsingSourceChoiceNoHitOutputAtFamily R t p q (level : Int)) :
    exists u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q),
      tailDependentEndpointRaceValue R t rho p q (level : Int) u = w.1 := by
  have hq : isingLeapfrogBoxBoundary R q := by
    unfold isingLeapfrogBoxBoundary
    rcases hqVertical with hq | hq
    · right; right; left; exact hq
    · right; right; right; omega
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1 w.2.2 with
    ⟨k, hkT, hkOutput, hkMinimal⟩
  have hcoord (l : Nat) (hl : l <= k) :=
    choiceRun_take_coordinates_eq_lineFree R t k p w.1 hkT hkMinimal l hl
  have hyEnd : lineFreeEndpoint (isingLeapfrogBoxInt p).2
      ((w.1.1.take k).map Prod.snd) = q.2.1 := by
    rw [← (hcoord k le_rfl).2, hkOutput]
  have hbottomInt : (rho : Int) <= (isingLeapfrogBoxInt p).2 := by
    unfold isingLeapfrogBoxInt
    dsimp
    exact_mod_cast hbottom
  have htopInt : (isingLeapfrogBoxInt p).2 + (rho : Int) <= R := by
    unfold isingLeapfrogBoxInt
    dsimp
    exact_mod_cast htop
  let hex : exists s, s <= k /\
      (lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take s).map Prod.snd) = (isingLeapfrogBoxInt p).2 - rho ∨
       lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take s).map Prod.snd) = (isingLeapfrogBoxInt p).2 + rho) := by
    rcases hqVertical with hqBottom | hqTop
    · have hend : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take k))).2 <=
          (isingLeapfrogBoxInt p).2 - rho := by
        rw [← lineFreeEndpoint_choiceVertical_full, hyEnd]
        have hq0 : ((q.2.1 : Nat) : Int) = 0 := by exact_mod_cast hqBottom
        rw [hq0]
        omega
      rcases exists_vertical_barrier_prefix_lower rho hρ
        (isingLeapfrogBoxInt p) (w.1.1.take k)
        hbottomInt hend with ⟨s, hs, heq⟩
      exact ⟨s, le_trans hs (List.length_take_le ..), Or.inl (by
        simpa [List.take_take,
          Nat.min_eq_left (le_trans hs (List.length_take_le ..))] using heq)⟩
    · have hend : (isingLeapfrogBoxInt p).2 + rho <=
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take k))).2 := by
        rw [← lineFreeEndpoint_choiceVertical_full, hyEnd]
        have hqR : ((q.2.1 : Nat) : Int) = R := by exact_mod_cast hqTop
        rw [hqR]
        omega
      rcases exists_vertical_barrier_prefix rho hρ
        (isingLeapfrogBoxInt p) (w.1.1.take k) k
        (by simp [hkT]) hbottomInt hend with ⟨s, hs, heq⟩
      exact ⟨s, le_trans hs (List.length_take_le ..), Or.inr (by
        simpa [List.take_take,
          Nat.min_eq_left (le_trans hs (List.length_take_le ..))] using heq)⟩
  let s := Nat.find hex
  have hsSpec := Nat.find_spec hex
  have hsK : s <= k := hsSpec.1
  have hsT : s <= t := hsK.trans hkT
  have havoid : forall l, l < s ->
      lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take l).map Prod.snd) ≠ (isingLeapfrogBoxInt p).2 - rho /\
      lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.1.take l).map Prod.snd) ≠ (isingLeapfrogBoxInt p).2 + rho := by
    intro l hl
    constructor <;> intro heq
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inl heq⟩
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inr heq⟩
  have hverticalFree (l : Nat) (hl : l < s) :
      lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ 0 /\
        lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ (2 * rho : Nat) := by
    have ha := havoid l hl
    have htr := lineFreeEndpoint_translate
      ((w.1.1.take l).map Prod.snd) (isingLeapfrogBoxInt p).2 (rho : Int)
    have ht : ((w.1.1.take s).map Prod.snd).take l =
        (w.1.1.take l).map Prod.snd := by
      simp [← List.map_take, List.take_take, Nat.min_eq_left hl.le]
    rw [ht, htr]
    constructor <;> intro heq
    · apply ha.1; omega
    · apply ha.2; push_cast at heq; omega
  have hverticalEnd : lineFreeEndpoint (rho : Int)
      ((w.1.1.take s).map Prod.snd) = 0 ∨
      lineFreeEndpoint (rho : Int) ((w.1.1.take s).map Prod.snd) =
        (2 * rho : Nat) := by
    have htr := lineFreeEndpoint_translate
      ((w.1.1.take s).map Prod.snd) (isingLeapfrogBoxInt p).2 (rho : Int)
    rw [htr]
    rcases hsSpec.2 with hs | hs
    · left; rw [hs]; ring
    · right; rw [hs]; push_cast; ring
  have hverticalFree' : forall l,
      l < ((w.1.1.take s).map Prod.snd).length ->
      lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ 0 /\
        lineFreeEndpoint (rho : Int)
          (((w.1.1.take s).map Prod.snd).take l) ≠ (2 * rho : Nat) := by
    intro l hl
    apply hverticalFree l
    simpa [w.1.2, hsT] using hl
  have hlineEnd := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
    (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
    ((w.1.1.take s).map Prod.snd) hverticalFree'
  let vword : IsingLineFirstBoundaryFamily rho s :=
    ⟨(w.1.1.take s).map Prod.snd, by simp [w.1.2, hsT], by
      unfold isingLineBoxBoundary
      have hendInt :
          ((isingLineChoiceRun (2 * rho) ⟨rho, by omega⟩
              ((w.1.1.take s).map Prod.snd)).1 : Int) = 0 ∨
            ((isingLineChoiceRun (2 * rho) ⟨rho, by omega⟩
              ((w.1.1.take s).map Prod.snd)).1 : Int) = (2 * rho : Nat) := by
        rw [hlineEnd]
        exact hverticalEnd
      exact_mod_cast hendInt, by
      intro l hl
      have hfreeL : forall r, r <
          (((w.1.1.take s).map Prod.snd).take l).length ->
          lineFreeEndpoint (rho : Int)
              ((((w.1.1.take s).map Prod.snd).take l).take r) ≠ 0 /\
            lineFreeEndpoint (rho : Int)
              ((((w.1.1.take s).map Prod.snd).take l).take r) ≠
                (2 * rho : Nat) := by
        intro r hr
        have hrl : r < l := lt_of_lt_of_le hr (List.length_take_le ..)
        have hrs : r < s := hrl.trans hl
        have hrs' : r <= min l s := Nat.le_min.mpr ⟨hrl.le, hrs.le⟩
        simpa [List.take_take, Nat.min_eq_left hrs', Nat.min_eq_left hrs.le] using
          hverticalFree r hrs
      have hrun := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
        (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
        (((w.1.1.take s).map Prod.snd).take l) hfreeL
      have hnot := hverticalFree l hl
      intro hb
      unfold isingLineBoxBoundary at hb
      rcases hb with hb | hb
      · apply hnot.1; rw [← hrun]; exact_mod_cast hb
      · apply hnot.2; rw [← hrun]; exact_mod_cast hb⟩
  let tail : IsingEndpointRaceTail t ⟨s, by omega⟩ :=
    ⟨w.1.1.drop s, by simp [w.1.2, hsT]⟩
  have hstop : firstVerticalBoundaryTimeEndpointFailure R
      (isingLeapfrogBoxInt p).2 (w.1.1.map Prod.snd) = k := by
    apply firstVerticalBoundaryTimeEndpointFailure_eq
    · simpa [w.1.2] using hkT
    · rw [← List.map_take, hyEnd]
      rcases hqVertical with hq0 | hqR
      · left; exact_mod_cast hq0
      · right; exact_mod_cast hqR
    · intro l hl
      have hc := hcoord l hl.le
      have hnot := hkMinimal l hl
      constructor
      · intro h0
        apply hnot
        unfold isingLeapfrogBoxBoundary
        right; right; left
        rw [← List.map_take, ← hc.2] at h0
        exact_mod_cast h0
      · intro hR
        apply hnot
        unfold isingLeapfrogBoxBoundary
        right; right; right
        rw [← List.map_take, ← hc.2] at hR
        have hR' : (isingLeapfrogChoiceRun R p (w.1.1.take l)).2.1 = R := by
          exact_mod_cast hR
        omega
  have hxPrefix : (w.1.1.map Prod.fst).take k =
      (w.1.1.take s).map Prod.fst ++
        ((w.1.1.drop s).map Prod.fst).take (k - s) := by
    rw [← List.map_take, ← List.map_take, ← List.map_append,
      ← List.take_add]
    congr 2
    omega
  have hxRaw : lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.1.map Prod.fst).take k) = q.1 := by
    rw [← List.map_take]
    exact (hcoord k le_rfl).1.symm.trans (by rw [hkOutput])
  have hendpoint : lineFreeEndpoint ((level : Int) - 1)
      ((w.1.1.take s).map Prod.fst) =
      sourceEndpointRaceTarget R t rho p q ⟨s, by omega⟩ vword tail := by
    have hstartX : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
    have hxRaw' : lineFreeEndpoint ((level : Int) - 1)
        ((w.1.1.map Prod.fst).take k) = q.1 := by
      rw [← hstartX]
      exact hxRaw
    rw [hxPrefix, lineFreeEndpoint_append_endpointFailure] at hxRaw'
    have htr := lineFreeEndpoint_translate
      (((w.1.1.drop s).map Prod.fst).take (k - s)) 0
      (lineFreeEndpoint ((level : Int) - 1)
        ((w.1.1.take s).map Prod.fst))
    unfold sourceEndpointRaceTarget
    dsimp only [vword, tail]
    rw [← List.map_append, List.take_append_drop, hstop]
    rw [htr] at hxRaw'
    change lineFreeEndpoint ((level : Int) - 1)
        ((w.1.1.take s).map Prod.fst) =
      (q.1.1 : Int) - lineFreeEndpoint 0
        (((w.1.1.drop s).map Prod.fst).take (k - s))
    linarith
  let hword : IsingHorizontalNoHitEndpointFamily s (level : Int)
      (sourceEndpointRaceTarget R t rho p q ⟨s, by omega⟩ vword tail) :=
    ⟨⟨(w.1.1.take s).map Prod.fst, by simp [w.1.2, hsT], by
      intro r hr
      have hrs : r <= s := by simpa [w.1.2, hsT] using hr
      have hav := w.2.1 r (hrs.trans hsT)
      have hstartX : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
      have hav' : lineFreeEndpoint ((level : Int) - 1)
          ((w.1.1.map Prod.fst).take r) ≠ level := by
        rw [← hstartX]
        exact hav
      simpa [← List.map_take, List.take_take, Nat.min_eq_left hrs] using hav'⟩,
      hendpoint⟩
  let u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
      (sourceEndpointRaceTarget R t rho p q) :=
    ⟨⟨s, by omega⟩, vword, tail, hword⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  dsimp [tailDependentEndpointRaceValue, u, hword, vword, tail]
  rw [prodBits_zip_self_endpointFailure, List.take_append_drop]

end
end StatMech.Universality
