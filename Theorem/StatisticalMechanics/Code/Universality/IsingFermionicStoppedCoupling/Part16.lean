/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part20


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem exists_vertical_barrier_prefix
    (rho : Nat) (hρ : 0 < rho) (start : Int × Int)
    (bs : List (Bool × Bool)) (j : Nat) (hj : j ≤ bs.length)
    (hlower : (rho : Int) ≤ start.2)
    (hupper : start.2 + rho ≤
      (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2)
    : ∃ s, s ≤ bs.length ∧
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) = start.2 + rho := by
  let swap : Int × Int → Int × Int := fun z => (z.2, z.1)
  let path := (isingLeapfrogChoiceSteps bs).map swap
  have hvalid : IsingDiagonalWalkStepsValid path := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    have he' := isingLeapfrogChoiceSteps_valid bs e he
    exact ⟨he'.2, he'.1⟩
  have hend : start.2 + rho ≤
      (isingDiagonalWalkEndpoint (start.2, start.1) path).1 := by
    have heq : (isingDiagonalWalkEndpoint (start.2, start.1) path).1 =
        (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2 := by
      unfold path swap isingDiagonalWalkEndpoint isingDiagonalWalkDisplacement
      simp only [List.map_map]
      rfl
    rw [heq]
    exact hupper
  rcases exists_prefix_fst_eq_of_lt_of_le path (start.2, start.1)
    (start.2 + rho) hvalid (by omega) hend with ⟨s, hs, heq⟩
  refine ⟨s, ?_, ?_⟩
  · simpa [path, isingLeapfrogChoiceSteps] using hs
  · have heq' :
        (isingDiagonalWalkEndpoint start
          ((isingLeapfrogChoiceSteps bs).take s)).2 = start.2 + rho := by
      simpa [path, swap, List.map_take, isingDiagonalWalkEndpoint,
        isingDiagonalWalkDisplacement] using heq
    calc
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) =
          (isingDiagonalWalkEndpoint start
            (isingLeapfrogChoiceSteps (bs.take s))).2 :=
        lineFreeEndpoint_choiceVertical_full (bs.take s) start
      _ = (isingDiagonalWalkEndpoint start
            ((isingLeapfrogChoiceSteps bs).take s)).2 := by
        simp [isingLeapfrogChoiceSteps, List.map_take]
      _ = start.2 + rho := heq'

theorem exists_vertical_barrier_prefix_lower
    (rho : Nat) (hρ : 0 < rho) (start : Int × Int)
    (bs : List (Bool × Bool))
    (hlower : (rho : Int) ≤ start.2)
    (hend : (isingDiagonalWalkEndpoint start
      (isingLeapfrogChoiceSteps bs)).2 ≤ start.2 - rho) :
    ∃ s, s ≤ bs.length ∧
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) = start.2 - rho := by
  let swap : Int × Int → Int × Int := fun z => (z.2, z.1)
  let path := (isingLeapfrogChoiceSteps bs).map swap
  have hvalid : IsingDiagonalWalkStepsValid path := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    have he' := isingLeapfrogChoiceSteps_valid bs e he
    exact ⟨he'.2, he'.1⟩
  have hend' : (isingDiagonalWalkEndpoint (start.2, start.1) path).1 ≤
      start.2 - rho := by
    have heq : (isingDiagonalWalkEndpoint (start.2, start.1) path).1 =
        (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2 := by
      unfold path swap isingDiagonalWalkEndpoint isingDiagonalWalkDisplacement
      simp only [List.map_map]
      rfl
    rw [heq]
    exact hend
  rcases exists_prefix_fst_eq_of_ge_of_gt path (start.2, start.1)
    (start.2 - rho) hvalid (by omega) hend' with ⟨s, hs, heq⟩
  refine ⟨s, ?_, ?_⟩
  · simpa [path, isingLeapfrogChoiceSteps] using hs
  · have heq' :
        (isingDiagonalWalkEndpoint start
          ((isingLeapfrogChoiceSteps bs).take s)).2 = start.2 - rho := by
      simpa [path, swap, List.map_take, isingDiagonalWalkEndpoint,
        isingDiagonalWalkDisplacement] using heq
    calc
      lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) =
          (isingDiagonalWalkEndpoint start
            (isingLeapfrogChoiceSteps (bs.take s))).2 :=
        lineFreeEndpoint_choiceVertical_full (bs.take s) start
      _ = (isingDiagonalWalkEndpoint start
            ((isingLeapfrogChoiceSteps bs).take s)).2 := by
        simp [isingLeapfrogChoiceSteps, List.map_take]
      _ = start.2 - rho := heq'

theorem isingLineChoiceRun_append_source
    (n : Nat) (p : IsingLineBox n) (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

theorem isingLineChoiceRun_boundary_source
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun]
      rw [show isingLineChoiceNext n p b = p by
        simp [isingLineChoiceNext, hp]]
      exact ih

theorem transverseWitness_of_barrier_exists
    (rho t : Nat) (level : Int) (hρ : 0 < rho)
    (start : Int × Int) (hstart : start.1 = level - 1) (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split)
    (j : Nat) (hj : j < split.before.length)
    (hex : ∃ s, s ≤ j ∧
      (lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 - rho ∨
       lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 + rho)) :
    ∃ z : IsingTransverseRaceWitnessFamily rho t level,
      transverseRaceWitnessValue rho t level z = w /\ (z.1 : Nat) <= j := by
  let s := Nat.find hex
  have hsSpec := Nat.find_spec hex
  have hsSpec' : s ≤ j ∧
      (lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 - rho ∨
       lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 + rho) := by
    simpa [s] using hsSpec
  have hsJ : s ≤ j := hsSpec'.1
  have hsT : s ≤ t := by
    have hbeforeLe : split.before.length ≤ t := by
      have hl := congrArg List.length (firstHitSplit_steps hsplit)
      simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps, w.2] at hl
      omega
    omega
  have havoid : ∀ l, l < s →
      lineFreeEndpoint start.2 ((w.1.take l).map Prod.snd) ≠ start.2 - rho ∧
      lineFreeEndpoint start.2 ((w.1.take l).map Prod.snd) ≠ start.2 + rho := by
    intro l hl
    constructor <;> intro heq
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inl heq⟩
    · exact (Nat.find_min hex hl) ⟨by omega, Or.inr heq⟩
  let hword : IsingHorizontalNoHitFamily s (level - 1) level :=
    ⟨(w.1.take s).map Prod.fst, by simp [w.2, hsT], by
      intro q hq heq
      have hqBefore : q < split.before.length := by omega
      have hfirst := firstHitSplit_firstHit hsplit q hqBefore
      apply hfirst
      have hsteps := congrArg (fun z : List (Int × Int) => z.take q)
        (firstHitSplit_steps hsplit)
      have hprefix : split.before.take q =
          (isingLeapfrogChoiceSteps w.1).take q := by
        simpa [IsingDiagonalWalkHitSplit.steps,
          List.take_append_of_le_length hqBefore.le] using hsteps
      calc
        (isingDiagonalWalkEndpoint start (split.before.take q)).1 =
            (isingDiagonalWalkEndpoint start
              ((isingLeapfrogChoiceSteps w.1).take q)).1 := by rw [hprefix]
        _ = (isingDiagonalWalkEndpoint start
              (isingLeapfrogChoiceSteps (w.1.take q))).1 := by
                simp [isingLeapfrogChoiceSteps, List.map_take]
        _ = lineFreeEndpoint start.1 ((w.1.take q).map Prod.fst) :=
          (lineFreeEndpoint_choiceHorizontal_full (w.1.take q) start).symm
        _ = lineFreeEndpoint (level - 1)
              (((w.1.take s).map Prod.fst).take q) := by
            rw [hstart]
            simp [List.map_take, List.take_take, Nat.min_eq_left hq]
        _ = level := heq⟩
  have hverticalFree : ∀ l, l < s →
      lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ 0 ∧
        lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ ((2 * rho : Nat) : Int) := by
    intro l hl
    have ha := havoid l hl
    have htranslate := lineFreeEndpoint_translate
      ((w.1.take l).map Prod.snd) start.2 (rho : Int)
    have htake : ((w.1.take s).map Prod.snd).take l =
        (w.1.take l).map Prod.snd := by
      simp [List.map_take, List.take_take, Nat.min_eq_left hl.le]
    rw [htake, htranslate]
    constructor <;> intro heq
    · apply ha.1
      omega
    · apply ha.2
      push_cast at heq
      omega
  have hverticalEnd :
      lineFreeEndpoint (rho : Int) ((w.1.take s).map Prod.snd) = 0 ∨
        lineFreeEndpoint (rho : Int) ((w.1.take s).map Prod.snd) =
          ((2 * rho : Nat) : Int) := by
    have htranslate := lineFreeEndpoint_translate
      ((w.1.take s).map Prod.snd) start.2 (rho : Int)
    rw [htranslate]
    rcases hsSpec'.2 with hs | hs
    · left; omega
    · right; push_cast; omega
  have hverticalFree' : ∀ l, l < ((w.1.take s).map Prod.snd).length →
      lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ 0 ∧
        lineFreeEndpoint (rho : Int)
          (((w.1.take s).map Prod.snd).take l) ≠ ((2 * rho : Nat) : Int) := by
    intro l hl
    apply hverticalFree l
    simpa [w.2, hsT] using hl
  have hlineEnd := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
    (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
    ((w.1.take s).map Prod.snd) hverticalFree' 
  let vword : IsingLineFirstBoundaryFamily rho s :=
    ⟨(w.1.take s).map Prod.snd, by simp [w.2, hsT], by
      unfold isingLineBoxBoundary
      have he : ((isingLineChoiceRun (2 * rho)
          (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
          ((w.1.take s).map Prod.snd)).1 : Int) = 0 ∨
        ((isingLineChoiceRun (2 * rho)
          (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
          ((w.1.take s).map Prod.snd)).1 : Int) = ((2 * rho : Nat) : Int) := by
        rw [hlineEnd]
        exact hverticalEnd
      exact_mod_cast he, by
      intro l hl
      unfold isingLineBoxBoundary
      have hfreeL : ∀ q, q < l →
          lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠ 0 ∧
            lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠
                ((2 * rho : Nat) : Int) := by
        intro q hq
        have hqS : q ≤ s := by omega
        simpa only [List.take_take, Nat.min_eq_left hq.le,
          Nat.min_eq_left hqS] using hverticalFree q (by omega)
      have hfreeL' : ∀ q,
          q < (((w.1.take s).map Prod.snd).take l).length →
          lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠ 0 ∧
            lineFreeEndpoint (rho : Int)
              ((((w.1.take s).map Prod.snd).take l).take q) ≠
                ((2 * rho : Nat) : Int) := by
        intro q hq
        apply hfreeL q
        rw [List.length_take] at hq
        omega
      have hrun := lineChoiceRun_val_eq_lineFreeEndpoint (2 * rho)
        (⟨rho, by omega⟩ : IsingLineBox (2 * rho))
        (((w.1.take s).map Prod.snd).take l) hfreeL'
      have hnot := hverticalFree l hl
      intro hb
      rcases hb with hb | hb
      · apply hnot.1
        rw [← hrun]
        exact_mod_cast hb
      · apply hnot.2
        rw [← hrun]
        exact_mod_cast hb⟩
  let tail : {tail : List (Bool × Bool) // tail.length = t - s} :=
    ⟨w.1.drop s, by simp [w.2, hsT]⟩
  let z : IsingTransverseRaceWitnessFamily rho t level :=
    ⟨⟨s, by omega⟩, hword, vword, tail⟩
  refine ⟨z, ?_, hsJ⟩
  · apply Subtype.ext
    dsimp [transverseRaceWitnessValue, z, hword, vword, tail]
    rw [prodBits_zip_self]
    exact List.take_append_drop s w.1


theorem sourceFailure_horizontal_or_transverse
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R)
    (w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) :
    (∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1) ∨
      ∃ z : IsingTransverseRaceWitnessFamily rho t (level : Int),
        transverseRaceWitnessValue rho t (level : Int) z = w.1 := by
  have hstartLt : (isingLeapfrogBoxInt p).1 < (level : Int) := by omega
  rcases sourceFailure_boundary_data R t p (level : Int) hstartLt w with
    ⟨split, j, hsplit, hj, hb, hminimal, hxlt, hrun⟩
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1
  have hfirst := firstHitSplit_firstHit hsplit
  have hpx : p.1.1 = level - 1 := by
    unfold isingLeapfrogBoxInt at hstart
    dsimp at hstart
    push_cast at hstart
    omega
  have hjT : j ≤ t := by
    have hl := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps, w.1.2] at hl
    omega
  have horizontal_of_xzero
      (hxzero : (isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 = 0) :
      ∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1 := by
    have hfree : ∀ l, l < ((w.1.1.take j).map Prod.fst).length →
        lineFreeEndpoint ((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Int)
            (((w.1.1.take j).map Prod.fst).take l) ≠ 0 ∧
          lineFreeEndpoint ((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Int)
            (((w.1.1.take j).map Prod.fst).take l) ≠ level := by
      intro l hl
      have hlj : l < j := by
        rw [List.length_map, List.length_take] at hl
        omega
      have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.take l) := by
        intro q hq
        rw [List.length_take] at hq
        have hql : q < l := by omega
        simpa [List.take_take, Nat.min_eq_left hql.le] using hminimal q (by omega)
      have hrunl := choiceExecValid_run_boxInt_eq_endpoint R p
        (w.1.1.take l) hexec
      have hrawx :
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take l))).1 =
          lineFreeEndpoint ((⟨level - 1, by omega⟩ : IsingLineBox level).1 : Int)
            (((w.1.1.take j).map Prod.fst).take l) := by
        calc
          _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
              ((w.1.1.take l).map Prod.fst) :=
            (lineFreeEndpoint_choiceHorizontal_full (w.1.1.take l)
              (isingLeapfrogBoxInt p)).symm
          _ = _ := by
            unfold isingLeapfrogBoxInt
            dsimp
            rw [hpx]
            simp [List.map_take, List.take_take, Nat.min_eq_left hlj.le]
      have hrunx := congrArg Prod.fst hrunl
      change ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take l))).1 at hrunx
      have hnbox := hminimal l hlj
      unfold isingLeapfrogBoxBoundary at hnbox
      constructor
      · intro heq
        apply hnbox
        left
        rw [hrawx] at hrunx
        have hz : ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) = 0 :=
          hrunx.trans heq
        exact_mod_cast hz
      · intro heq
        have hx := hfirst.endpoint_take_fst_lt split hvalid hstartLt l (by omega)
        have hsteps := congrArg (fun z : List (Int × Int) => z.take l)
          (firstHitSplit_steps hsplit)
        have hprefix : split.before.take l =
            (isingLeapfrogChoiceSteps w.1.1).take l := by
          simpa [IsingDiagonalWalkHitSplit.steps,
            List.take_append_of_le_length (show l ≤ split.before.length by omega)]
            using hsteps
        rw [hprefix] at hx
        have hx' : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take l))).1 < level := by
          simpa [isingLeapfrogChoiceSteps, List.map_take] using hx
        rw [hrawx] at hx'
        omega
    have hlinePrefix := lineChoiceRun_val_eq_lineFreeEndpoint level
      (⟨level - 1, by omega⟩ : IsingLineBox level)
      ((w.1.1.take j).map Prod.fst) hfree
    have hrawJ := congrArg Prod.fst hrun
    have hlinePrefixZero : isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level)
          ((w.1.1.take j).map Prod.fst) = ⟨0, by omega⟩ := by
      apply Fin.ext
      have hlineInt : ((isingLineChoiceRun level
          (⟨level - 1, by omega⟩ : IsingLineBox level)
            ((w.1.1.take j).map Prod.fst)).1 : Int) = 0 := by
        rw [hlinePrefix]
        have hfreeJ := lineFreeEndpoint_choiceHorizontal_full
          (w.1.1.take j) (isingLeapfrogBoxInt p)
        have hrawJ' := congrArg Prod.fst hrun
        change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hrawJ'
        have hstartInt : (isingLeapfrogBoxInt p).1 =
            ((level - 1 : Nat) : Int) := by
          unfold isingLeapfrogBoxInt
          dsimp
          exact_mod_cast hpx
        change lineFreeEndpoint ((level - 1 : Nat) : Int)
          ((w.1.1.take j).map Prod.fst) = 0
        rw [← hstartInt, hfreeJ, ← hrawJ']
        exact_mod_cast hxzero
      change (isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level)
          ((w.1.1.take j).map Prod.fst)).1 = 0
      exact_mod_cast hlineInt
    let fullx := w.1.1.map Prod.fst
    have hdecomp : fullx = ((w.1.1.take j).map Prod.fst) ++
        ((w.1.1.drop j).map Prod.fst) := by
      dsimp [fullx]
      rw [← List.map_append, List.take_append_drop]
    have hlineFull : isingLineChoiceRun level
        (⟨level - 1, by omega⟩ : IsingLineBox level) fullx =
        ⟨0, by omega⟩ := by
      rw [hdecomp, isingLineChoiceRun_append_source, hlinePrefixZero]
      exact isingLineChoiceRun_boundary_source level ⟨0, by omega⟩
        (by simp [isingLineBoxBoundary]) _
    refine ⟨⟨w.1, ?_⟩, rfl⟩
    simpa [IsingLeapfrogHorizontalEscapeFamily, fullx, hpx] using hlineFull
  unfold isingLeapfrogBoxBoundary at hb
  rcases hb with hx0 | hxR | hy0 | hyR
  · exact Or.inl (horizontal_of_xzero hx0)
  · exfalso
    have hxrun := congrArg Prod.fst hrun
    change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hxrun
    push_cast at hxR
    omega
  · right
    have hyEnd : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take j))).2 ≤
          (isingLeapfrogBoxInt p).2 - rho := by
      have hyrun := congrArg Prod.snd hrun
      change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hyrun
      push_cast at hy0
      have hbottomInt : (rho : Int) ≤ (isingLeapfrogBoxInt p).2 := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom
      omega
    rcases exists_vertical_barrier_prefix_lower rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.take j) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1 split hsplit j hj (by
        have hsJ : s ≤ j := le_trans hs (List.length_take_le ..)
        exact ⟨s, hsJ, Or.inl (by
          simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩) with
      ⟨z, hz, hzj⟩
    exact ⟨z, hz⟩
  · right
    have hyEnd : (isingLeapfrogBoxInt p).2 + rho ≤
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j))).2 := by
      have hyrun := congrArg Prod.snd hrun
      change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hyrun
      push_cast at hyR
      have htopInt : (isingLeapfrogBoxInt p).2 + (rho : Int) ≤ R := by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast htop
      omega
    rcases exists_vertical_barrier_prefix rho hρ
      (isingLeapfrogBoxInt p) (w.1.1.take j) j (by simp [hjT]) (by
        unfold isingLeapfrogBoxInt
        dsimp
        exact_mod_cast hbottom) hyEnd with ⟨s, hs, heq⟩
    rcases transverseWitness_of_barrier_exists rho t (level : Int) hρ
      (isingLeapfrogBoxInt p) (by omega) w.1 split hsplit j hj (by
        have hsJ : s ≤ j := le_trans hs (List.length_take_le ..)
        exact ⟨s, hsJ, Or.inr (by
          simpa [List.take_take, Nat.min_eq_left hsJ] using heq)⟩) with
      ⟨z, hz, hzj⟩
    exact ⟨z, hz⟩

end
end StatMech.Universality
