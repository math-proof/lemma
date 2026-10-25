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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem exists_sourceFailureOutputFarCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    ∃ z : IsingEndpointFarEscapeWitnessFamily level t
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2,
      endpointFarEscapeWitnessValue level t
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 z = w.1.1 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w.1 with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hjT : j ≤ t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.1.2] at hlen
    omega
  have hprefixQ : isingLeapfrogChoiceRun R p (w.1.1.1.take j) = q := by
    have hdecomp : w.1.1.1 = w.1.1.1.take j ++ w.1.1.1.drop j :=
      (List.take_append_drop j w.1.1.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1.1.1 =
        isingLeapfrogChoiceRun R p (w.1.1.1.take j) := by
      calc
        _ = isingLeapfrogChoiceRun R p
            (w.1.1.1.take j ++ w.1.1.1.drop j) := by rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.1.1.take j))
              (w.1.1.1.drop j) := isingLeapfrogChoiceRun_append_full ..
        _ = _ :=
          isingLeapfrogChoiceRun_of_boundary_endpointFailure R _ hb _
    exact hfull.symm.trans w.2
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1.1
  have hpx : (isingLeapfrogBoxInt p).1 = (level : Int) - 1 := by omega
  have hpxNat : p.1.1 = level - 1 := by
    unfold isingLeapfrogBoxInt at hstart
    dsimp at hstart
    omega
  let xbits := (w.1.1.1.take j).map Prod.fst
  let ybits := (w.1.1.1.take j).map Prod.snd
  have hxlen : xbits.length = j := by simp [xbits, w.1.1.2, hjT]
  have hylen : ybits.length = j := by simp [ybits, w.1.1.2, hjT]
  have hxfree : ∀ l, l < xbits.length →
      lineFreeEndpoint
          (((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Nat) : Int)
          (xbits.take l) ≠ 0 ∧
        lineFreeEndpoint
          (((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Nat) : Int)
          (xbits.take l) ≠ level := by
    intro l hl
    have hlj : l < j := by simpa [hxlen] using hl
    have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.1.take l) := by
      intro r hr
      rw [List.length_take] at hr
      have hrl : r < l := by omega
      simpa [List.take_take, Nat.min_eq_left hrl.le] using
        hminimal r (hrl.trans hlj)
    have hrunl := choiceExecValid_run_boxInt_eq_endpoint R p
      (w.1.1.1.take l) hexec
    have hrawx :
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take l))).1 =
        lineFreeEndpoint
          (((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Nat) : Int)
          (xbits.take l) := by
      calc
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.1.take l).map Prod.fst) :=
          (lineFreeEndpoint_choiceHorizontal_full
            (w.1.1.1.take l) (isingLeapfrogBoxInt p)).symm
        _ = _ := by
          unfold isingLeapfrogBoxInt
          dsimp
          rw [hpxNat]
          simp [xbits, List.map_take, List.take_take,
            Nat.min_eq_left hlj.le]
    have hrunx := congrArg Prod.fst hrunl
    change ((isingLeapfrogChoiceRun R p (w.1.1.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.1.take l))).1 at hrunx
    constructor
    · intro heq
      have hb0 := hminimal l hlj
      apply hb0
      unfold isingLeapfrogBoxBoundary
      left
      rw [hrawx] at hrunx
      exact_mod_cast hrunx.trans heq
    · intro heq
      have hfirst := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt
        split hvalid hstartLt l (by omega)
      have hsteps := congrArg (fun z : List (Int × Int) => z.take l)
        (firstHitSplit_steps hsplit)
      have hprefix : split.before.take l =
          (isingLeapfrogChoiceSteps w.1.1.1).take l := by
        simpa [IsingDiagonalWalkHitSplit.steps,
          List.take_append_of_le_length (show l ≤ split.before.length by omega)]
          using hsteps
      rw [hprefix] at hfirst
      have hfirst' : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take l))).1 < level := by
        simpa [isingLeapfrogChoiceSteps, List.map_take] using hfirst
      rw [hrawx, heq] at hfirst'
      omega
  have hlineEnd : isingLineChoiceRun level
      (⟨level - 1, by omega⟩ : IsingLineBox level) xbits = ⟨0, by omega⟩ := by
    apply Fin.ext
    have hrunLine := lineChoiceRun_val_eq_lineFreeEndpoint level
      (⟨level - 1, by omega⟩ : IsingLineBox level) xbits hxfree
    have hlineInt : ((isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level) xbits).1 : Int) = 0 := by
      rw [hrunLine]
      have hfreeJ := lineFreeEndpoint_choiceHorizontal_full
        (w.1.1.1.take j) (isingLeapfrogBoxInt p)
      have hrawJ := congrArg Prod.fst hrun
      change ((isingLeapfrogChoiceRun R p (w.1.1.1.take j)).1.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.1.take j))).1 at hrawJ
      have hstartInt : (isingLeapfrogBoxInt p).1 =
          ((level - 1 : Nat) : Int) := by
        unfold isingLeapfrogBoxInt
        dsimp
        rw [hpxNat]
      change lineFreeEndpoint ((level - 1 : Nat) : Int) xbits = 0
      rw [show xbits = (w.1.1.1.take j).map Prod.fst by rfl,
        ← hstartInt, hfreeJ, ← hrawJ, hprefixQ]
      exact_mod_cast hqLeft
    change (isingLineChoiceRun level
      (⟨level - 1, by omega⟩ : IsingLineBox level) xbits).1 = 0
    exact_mod_cast hlineInt
  let xword : IsingLineFarFirstBoundaryFamily level j :=
    ⟨xbits, hxlen, hlineEnd, by
      intro l hl
      unfold isingLineBoxBoundary
      have hf := hxfree l (by simpa [hxlen] using hl)
      have hrunLine := lineChoiceRun_val_eq_lineFreeEndpoint level
        (⟨level - 1, by omega⟩ : IsingLineBox level) (xbits.take l) (by
          intro r hr
          have hrlSmall : r < l := by
            rw [List.length_take] at hr
            omega
          have hrl : r < xbits.length := by
            omega
          simpa [List.take_take, Nat.min_eq_left hrlSmall.le] using
            hxfree r hrl)
      intro hbLine
      rcases hbLine with hb0 | hbR
      · apply hf.1
        rw [← hrunLine]
        exact_mod_cast hb0
      · apply hf.2
        rw [← hrunLine]
        exact_mod_cast hbR⟩
  let yword : VerticalChoicePathFamily j
      (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 :=
    ⟨ybits, hylen, by
      rw [lineFreeEndpoint_choiceVertical_full]
      have hry := congrArg Prod.snd hrun
      rw [hprefixQ] at hry
      simpa [ybits] using hry.symm⟩
  let tail : {tail : List (Bool × Bool) // tail.length = t - j} :=
    ⟨w.1.1.1.drop j, by simp [w.1.1.2, hjT]⟩
  refine ⟨⟨⟨j, by omega⟩, xword, yword, tail⟩, ?_⟩
  apply Subtype.ext
  change (((w.1.1.1.take j).map Prod.fst).zip
      ((w.1.1.1.take j).map Prod.snd)) ++ w.1.1.1.drop j = w.1.1.1
  rw [prodBits_zip_self_endpointFailure]
  exact List.take_append_drop _ w.1.1.1

end
end StatMech.Universality
