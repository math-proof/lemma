/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_rotatePoint_add (c : Fin 4) (p q : ℤ × ℤ) :
    ons_rotatePoint c (p + q) =
      ons_rotatePoint c p + ons_rotatePoint c q := by
  fin_cases c <;> apply Prod.ext <;> simp [ons_rotatePoint] <;> ring

theorem ons_rotatePoint_nsmul (c : Fin 4) (k : ℕ) (p : ℤ × ℤ) :
    ons_rotatePoint c (k • p) = k • ons_rotatePoint c p := by
  induction k with
  | zero => fin_cases c <;> simp [ons_rotatePoint]
  | succ k ih => rw [succ_nsmul, succ_nsmul, ons_rotatePoint_add, ih]

theorem ons_rotatePoint_injective (c : Fin 4) :
    Function.Injective (ons_rotatePoint c) := by
  intro p q h
  fin_cases c <;>
    have hfst := congrArg Prod.fst h <;>
    have hsnd := congrArg Prod.snd h <;>
    apply Prod.ext <;>
    simp [ons_rotatePoint] at hfst hsnd ⊢ <;> omega

theorem ons_stepOf_add_direction (c d : Fin 4) :
    stepOf (d + c) = ons_rotatePoint c (stepOf d) := by
  fin_cases c <;> fin_cases d <;> rfl

theorem ons_pathDisplacement_map_add
    (c : Fin 4) (l : List (Fin 4)) :
    ons_pathDisplacement (l.map (fun d ↦ d + c)) =
      ons_rotatePoint c (ons_pathDisplacement l) := by
  induction l with
  | nil => fin_cases c <;> rfl
  | cons d ds ih =>
      simp only [List.map_cons, ons_pathDisplacement_cons, ih,
        ons_stepOf_add_direction, ons_rotatePoint_add]

theorem ons_pos_add_direction {n : ℕ} [NeZero n]
    (c : Fin 4) (d : Fin n → Fin 4) (i : Fin n) :
    pos (fun j ↦ d j + c) i = ons_rotatePoint c (pos d i) := by
  unfold pos
  induction (Finset.univ.filter (fun x ↦ x < i)) using Finset.induction with
  | empty => fin_cases c <;> rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
        ons_stepOf_add_direction, ons_rotatePoint_add]

theorem ons_periodStateCoord_add_direction
    {n : ℕ} [NeZero n]
    (c : Fin 4) (d : Fin n → Fin 4) (z : ℕ × Fin n) :
    ons_periodStateCoord (fun i ↦ d i + c) z =
      ons_rotatePoint c (ons_periodStateCoord d z) := by
  have hlist : List.ofFn (fun i ↦ d i + c) =
      (List.ofFn d).map (fun e ↦ e + c) := by
    rw [List.map_ofFn]
    congr 1
  have hdisp : ons_pathDisplacement (List.ofFn (fun i ↦ d i + c)) =
      ons_rotatePoint c (ons_pathDisplacement (List.ofFn d)) := by
    rw [hlist, ons_pathDisplacement_map_add]
  rw [ons_periodStateCoord, ons_periodStateCoord,
    ons_pos_add_direction, hdisp, ← ons_rotatePoint_nsmul,
    ← ons_rotatePoint_add]

theorem ons_turnPow_add_both (a b c : Fin 4) :
    ons_turnPow (a + c) (b + c) = ons_turnPow a b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem ons_cyclicTurnSum_ofFn_add_direction
    {n : ℕ} [NeZero n] (c : Fin 4) (d : Fin n → Fin 4) :
    ons_cyclicTurnSum (List.ofFn (fun i ↦ d i + c)) =
      ons_cyclicTurnSum (List.ofFn d) := by
  rw [ons_cyclicTurnSum_ofFn', ons_cyclicTurnSum_ofFn']
  apply Finset.sum_congr rfl
  intro i hi
  exact ons_turnPow_add_both (d i) (d (i + 1)) c

theorem ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hinj : Function.Injective (ons_periodStateCoord d))
    (hne : (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨
      (ons_pathDisplacement (List.ofFn d)).2 ≠ 0) :
    ons_cyclicTurnSum (List.ofFn d) = 0 := by
  let D := ons_pathDisplacement (List.ofFn d)
  change D.1 ≠ 0 ∨ D.2 ≠ 0 at hne
  let solve (c : Fin 4)
      (hpos : 0 < (ons_rotatePoint c D).1) :
      ons_cyclicTurnSum (List.ofFn d) = 0 := by
    let dr : Fin n → Fin 4 := fun i ↦ d i + c
    have hcoord : ∀ z, ons_periodStateCoord dr z =
        ons_rotatePoint c (ons_periodStateCoord d z) :=
      ons_periodStateCoord_add_direction c d
    have hinjr : Function.Injective (ons_periodStateCoord dr) := by
      intro x y hxy
      apply hinj
      apply ons_rotatePoint_injective c
      rw [← hcoord x, ← hcoord y]
      exact hxy
    have hDr : 0 < (ons_pathDisplacement (List.ofFn dr)).1 := by
      rw [show List.ofFn dr = (List.ofFn d).map (fun e ↦ e + c) by
        rw [List.map_ofFn]
        congr 1]
      rw [ons_pathDisplacement_map_add]
      exact hpos
    have hz := ons_periodicSimple_cyclicTurnSum_eq_zero dr hinjr hDr
    rw [ons_cyclicTurnSum_ofFn_add_direction c d] at hz
    exact hz
  by_cases hx0 : D.1 = 0
  · have hy : D.2 ≠ 0 := hne.resolve_left (not_ne_iff.mpr hx0)
    by_cases hyp : 0 < D.2
    · exact solve 3 (by simpa [ons_rotatePoint] using hyp)
    · exact solve 1 (by
        have : D.2 < 0 := lt_of_le_of_ne (le_of_not_gt hyp) hy
        simpa [ons_rotatePoint] using neg_pos.mpr this)
  · by_cases hxp : 0 < D.1
    · exact solve 0 (by simpa [ons_rotatePoint] using hxp)
    · exact solve 2 (by
        have : D.1 < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
        simpa [ons_rotatePoint] using neg_pos.mpr this)

theorem ons_liftDir_periodStateCoord_eq_periodicLiftVertex
    {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my)
    (z : ℕ × Fin n) :
    ons_periodStateCoord (ons_liftDir v) z =
      ons_periodicLiftVertex v mx my (z.1 : ℤ) z.2 := by
  rw [ons_periodStateCoord, ons_periodicLiftVertex]
  have hdisp : ons_pathDisplacement (List.ofFn (ons_liftDir v)) =
      ons_windingTranslation L mx my := by
    rw [ons_pathDisplacement_ofFn]
    exact ons_liftDir_totalStep_eq_windingTranslation v mx my hmx hmy
  rw [hdisp]
  unfold ons_windingTranslation
  apply Prod.ext <;> simp [Prod.smul_mk] <;> ring

theorem ons_liftDir_periodStateCoord_injective
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (mx my : ℤ) (hne : mx ≠ 0 ∨ my ≠ 0)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
    Function.Injective (ons_periodStateCoord (ons_liftDir v)) := by
  intro x y hxy
  have hp : ons_periodicLiftVertex v mx my (x.1 : ℤ) x.2 =
      ons_periodicLiftVertex v mx my (y.1 : ℤ) y.2 := by
    rw [← ons_liftDir_periodStateCoord_eq_periodicLiftVertex
      v mx my hmx hmy x,
      ← ons_liftDir_periodStateCoord_eq_periodicLiftVertex
      v mx my hmx hmy y]
    exact hxy
  have hpair : ((x.1 : ℤ), x.2) = ((y.1 : ℤ), y.2) :=
    (ons_periodicLiftVertex_injective
      v hvalid hsite mx my hne) hp
  apply Prod.ext
  · exact Int.ofNat_inj.mp
      (congrArg (fun z : ℤ × Fin n ↦ z.1) hpair)
  · exact congrArg (fun z : ℤ × Fin n ↦ z.2) hpair

theorem ons_liftDir_displacement_nonzero
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L) (mx my : ℤ)
    (hne : mx ≠ 0 ∨ my ≠ 0)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
    (ons_pathDisplacement (List.ofFn (ons_liftDir v))).1 ≠ 0 ∨
      (ons_pathDisplacement (List.ofFn (ons_liftDir v))).2 ≠ 0 := by
  rw [ons_pathDisplacement_ofFn,
    ons_liftDir_totalStep_eq_windingTranslation v mx my hmx hmy]
  unfold ons_windingTranslation
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rcases hne with hx | hy
  · left
    exact mul_ne_zero hL hx
  · right
    exact mul_ne_zero hL hy

theorem ons_noncontractible_liftDir_cyclicTurnSum_eq_zero
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
    ons_cyclicTurnSum (List.ofFn (ons_liftDir v)) = 0 := by
  obtain ⟨mx, my, hmx, hmy, hne, -⟩ :=
    ons_simpleLoop_nonzeroHomology_periodicLift
      v hvalid hsite hnu hhom
  apply ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    (ons_liftDir v)
    (ons_liftDir_periodStateCoord_injective
      v hvalid hsite mx my hne hmx hmy)
    (ons_liftDir_displacement_nonzero v mx my hne hmx hmy)

theorem ons_noncontractible_turnProduct_eq_one
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (omega : ℂ) (homega : omega ≠ 0)
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
    ∏ k, ons_turnW omega (v (k + 1)).2 (v k).2 = 1 := by
  rw [ons_liftDir_turnProduct omega v]
  calc
    (∏ k, ons_turnW omega (ons_liftDir v k)
        (ons_liftDir v (k + 1))) =
        ∏ k, omega ^ ons_turnPow (ons_liftDir v k)
          (ons_liftDir v (k + 1)) := by
      apply Finset.prod_congr rfl
      intro k hk
      exact ons_turnW_eq_zpow omega _ _
        (ons_liftDir_nonUturn v hnu k)
    _ = omega ^ (∑ k, ons_turnPow (ons_liftDir v k)
          (ons_liftDir v (k + 1))) :=
      ons_prod_zpow omega homega _ _
    _ = 1 := by
      have hz := ons_noncontractible_liftDir_cyclicTurnSum_eq_zero
        v hvalid hsite hnu hhom
      rw [ons_cyclicTurnSum_ofFn'] at hz
      rw [hz]
      simp

theorem ons_decExpanded_turnProduct_eq_one_of_nonzeroHomology
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (hhom : ons_evenHomology L (ons_walkOriginalEdges q) ≠ 0) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∏ k, ons_turnW ons_turnRoot
        (ons_decExpandedKWLoop L q hq (k + 1)).2
        (ons_decExpandedKWLoop L q hq k).2 = 1 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hroot : ons_turnRoot ≠ 0 := by
    intro h
    have hs := ons_turnRoot_sq
    rw [h] at hs
    have hs' : (0 : ℂ) = Complex.I := by simpa using hs
    exact Complex.I_ne_zero hs'.symm
  have hrefined : ons_evenHomology (8 * L)
      (ons_dartEdgeSet (ons_decExpandedKWLoop L q hq)) ≠ 0 := by
    rw [ons_decExpandedKWLoop_edgeSet L q hq]
    rw [ons_decEmbedWalk_evenHomology_eq L q hq hsnd]
    exact hhom
  exact ons_noncontractible_turnProduct_eq_one
    ons_turnRoot hroot (ons_decExpandedKWLoop L q hq)
    (ons_decExpandedKWLoop_valid L q hq)
    (ons_decExpandedKWLoop_site_injective L q hq)
    (ons_decExpandedKWLoop_nonUturn L q hq) hrefined

end StatMech.Onsager
