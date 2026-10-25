/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackBoundary_strandStep_eq_medialStep_add_potential
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    let a := stepOf (fkRectBlackBoundaryMedialDirection pairing d)
    let p := fkRectMedialSidePotential d.1.2
    let q := fkRectMedialSidePotential
      ((fkMedialBlackBoundaryPerm pairing d).1.2)
    stepOf (fkMedialStrandDirection pairing d.1) =
      (a.1 + a.2 + q.1 - p.1, a.1 - a.2 + q.2 - p.2) := by
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkRectBlackBoundaryMedialDirection, fkRectMedialSideDirection,
      fkRectMedialSidePotential, fkMedialBlackBoundaryPerm_val,
      fkMedialBoundaryStep_apply, fkMedialLocalMate, fkMedialBondMate,
      fkMedialStrandDirection, hp, stepOf]

theorem fkRectBlackOrbitList_get_add_one
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    (fkRectBlackOrbitList pairing d).get (i + 1) =
      fkMedialBlackBoundaryPerm pairing
        ((fkRectBlackOrbitList pairing d).get i) := by
  let p := fkMedialBlackBoundaryPerm pairing
  let l := fkRectBlackOrbitList pairing d
  have hl : (fkRectBlackOrbitList pairing d).Nodup :=
    Equiv.Perm.nodup_toList p d
  have hnextList := List.next_getElem
    (fkRectBlackOrbitList pairing d) hl i.val i.isLt
  have happly := Equiv.Perm.next_toList_eq_apply p d
    ((fkRectBlackOrbitList pairing d).get i)
    (List.get_mem (fkRectBlackOrbitList pairing d) i)
  have happly' : (fkRectBlackOrbitList pairing d).next
      (fkRectBlackOrbitList pairing d)[i.val] (by
        exact List.getElem_mem (l := fkRectBlackOrbitList pairing d) i.isLt) =
      p (fkRectBlackOrbitList pairing d)[i.val] := by
    simpa [l, p, List.get_eq_getElem] using happly
  rw [happly'] at hnextList
  have hiv : (i + 1).val =
      (i.val + 1) % (fkRectBlackOrbitList pairing d).length := by
    simp [Fin.val_add, Nat.add_mod]
  simpa only [p, List.get_eq_getElem, hiv] using hnextList.symm


theorem fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let medial := ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing
        ((fkRectBlackOrbitList pairing d).get i))
    ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection pairing d)) =
      (medial.1 + medial.2, medial.1 - medial.2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hn.ne'⟩
  let e : Fin l.length → FKMedialBlackDart R.medialTorus := l.get
  let a : Fin l.length → Int × Int := fun i =>
    stepOf (fkRectBlackBoundaryMedialDirection pairing (e i))
  let p : Fin l.length → Int × Int := fun i =>
    fkRectMedialSidePotential (e i).1.2
  have hnext (i : Fin l.length) :
      e (i + 1) = fkMedialBlackBoundaryPerm pairing (e i) := by
    exact fkRectBlackOrbitList_get_add_one pairing d i
  have hpoint (i : Fin l.length) :
      stepOf (fkRectBlackOrbitDirection pairing d i) =
        ((a i).1 + (a i).2 + (p (i + 1)).1 - (p i).1,
          (a i).1 - (a i).2 + (p (i + 1)).2 - (p i).2) := by
    have h := fkRectBlackBoundary_strandStep_eq_medialStep_add_potential
      pairing (e i)
    rw [← hnext i] at h
    exact h
  have hpot (coord : (Int × Int) → Int) :
      (∑ i, coord (p (i + 1))) = ∑ i, coord (p i) := by
    change (∑ i, (fun j => coord (p j))
      ((Equiv.addRight (1 : Fin l.length)) i)) = _
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin l.length))
      (fun i => coord (p i))
  rw [ons_pathDisplacement_ofFn, ons_pathDisplacement_ofFn]
  change (∑ i, stepOf (fkRectBlackOrbitDirection pairing d i)) =
    ((∑ i, a i).1 + (∑ i, a i).2,
      (∑ i, a i).1 - (∑ i, a i).2)
  rw [show (∑ i, stepOf (fkRectBlackOrbitDirection pairing d i)) =
      ∑ i, ((a i).1 + (a i).2 + (p (i + 1)).1 - (p i).1,
        (a i).1 - (a i).2 + (p (i + 1)).2 - (p i).2) by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpoint i]
  apply Prod.ext
  · simp only [Prod.fst_sum, Prod.snd_sum]
    dsimp only [a]
    simp only [Prod.fst, Prod.snd, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.fst]
    ring
  · simp only [Prod.fst_sum, Prod.snd_sum]
    dsimp only [a]
    simp only [Prod.fst, Prod.snd, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.snd]
    ring


theorem fkRectBlackOrbitDisplacement_eq_two_deck_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection
          (fkRectConfigurationToMedialPairing R omega) d)) =
      2 • fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let D := ons_pathDisplacement
    (List.ofFn (fkRectBlackOrbitDirection pairing d))
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have htrace : fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 n = w := by
    simpa [pairing, n, w] using
      (fkRectBlackBoundaryPrimalCycleWalk_winding R omega d).symm
  have hcenter := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d.1 (0, 0) n
  rw [hdart, htrace] at hcenter
  have hcenter' : fkRectRefinedBoundaryCenterAfter pairing d.1
      (fkRectRefinedBoundaryCanonicalCenter R d.1) n =
        ((fkRectRefinedBoundaryCanonicalCenter R d.1).1 +
            4 * (fkRectSquareDeckTranslation R w).1,
          (fkRectRefinedBoundaryCanonicalCenter R d.1).2 +
            4 * (fkRectSquareDeckTranslation R w).2) := by
    simpa only [Prod.fst, Prod.snd, add_zero, add_sub_cancel_right] using hcenter
  have hpointShift :
      fkRectBlackBoundaryPointAfter R pairing d n =
        fkRectBlackDartShiftedPoint R w d := by
    unfold fkRectBlackBoundaryPointAfter fkRectBlackDartShiftedPoint
    rw [hblack, hcenter']
  have hpointPrefix := fkRectBlackBoundaryPointAfter_eq_prefix
    R pairing d n
  have hprefix := fkRectBlackOrbitPrefix_length_eq_displacement pairing d
  change fkRectBlackOrbitPrefix pairing d n = D at hprefix
  rw [hprefix] at hpointPrefix
  have hshift := fkRectBlackDartShiftedPoint_add R (0, 0) w d
  have hstart : fkRectBlackDartShiftedPoint R (0, 0) d =
      fkRectBlackBoundaryPointAfter R pairing d 0 := by
    rw [fkRectBlackBoundaryPointAfter_zero]
  have hzeroAdd : ((0, 0) : Int × Int) + w = w := by
    apply Prod.ext <;> simp
  rw [hzeroAdd, hstart] at hshift
  have heq : 2 • D = fkRectBlackDeckPointShift R w := by
    apply add_left_cancel
    calc
      fkRectBlackBoundaryPointAfter R pairing d 0 + 2 • D =
          fkRectBlackBoundaryPointAfter R pairing d n := hpointPrefix.symm
      _ = fkRectBlackDartShiftedPoint R w d := hpointShift
      _ = fkRectBlackBoundaryPointAfter R pairing d 0 +
          fkRectBlackDeckPointShift R w := hshift
  change D = 2 • fkRectSquareDeckTranslation R w
  apply Prod.ext
  · have hx := congrArg Prod.fst heq
    unfold fkRectBlackDeckPointShift at hx
    change 2 * D.1 = 4 * (fkRectSquareDeckTranslation R w).1 at hx
    change D.1 = 2 * (fkRectSquareDeckTranslation R w).1
    omega
  · have hy := congrArg Prod.snd heq
    unfold fkRectBlackDeckPointShift at hy
    change 2 * D.2 = 4 * (fkRectSquareDeckTranslation R w).2 at hy
    change D.2 = 2 * (fkRectSquareDeckTranslation R w).2
    omega


theorem fkRectBlackOrbitMedialDisplacement_eq_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing
        ((fkRectBlackOrbitList pairing d).get i)) =
      (((2 * R.width : ℕ) : ℤ) * w.1, (R.height : ℤ) * w.2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let medial := ons_pathDisplacement (List.ofFn fun i =>
    fkRectBlackBoundaryMedialDirection pairing
      ((fkRectBlackOrbitList pairing d).get i))
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hdiag :=
    fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement R omega d
  have hdeck := fkRectBlackOrbitDisplacement_eq_two_deck_winding R omega d
  change ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection pairing d)) =
        (medial.1 + medial.2, medial.1 - medial.2) at hdiag
  change ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection pairing d)) =
        2 • fkRectSquareDeckTranslation R w at hdeck
  have heq : (medial.1 + medial.2, medial.1 - medial.2) =
      2 • fkRectSquareDeckTranslation R w := hdiag.symm.trans hdeck
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  have hheight : (2 : ℤ) * (R.height / 2 : ℕ) = R.height := by
    exact_mod_cast Nat.two_mul_div_two_of_even R.height_even
  unfold fkRectSquareDeckTranslation at hx hy
  change medial.1 + medial.2 =
    2 * ((R.width : ℤ) * w.1 + (R.height / 2 : ℕ) * w.2) at hx
  change medial.1 - medial.2 =
    2 * ((R.width : ℤ) * w.1 - (R.height / 2 : ℕ) * w.2) at hy
  change medial = _
  apply Prod.ext
  · change medial.1 = ((2 * R.width : ℕ) : ℤ) * w.1
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have htwo : 2 * medial.1 = 4 * (R.width : ℤ) * w.1 := by
      linear_combination hx + hy
    have htarget : 2 * medial.1 =
        2 * (2 * (R.width : ℤ) * w.1) := by
      calc
        _ = 4 * (R.width : ℤ) * w.1 := htwo
        _ = _ := by ring
    omega
  · change medial.2 = (R.height : ℤ) * w.2
    have htwo : 2 * medial.2 = 4 * (R.height / 2 : ℕ) * w.2 := by
      linear_combination hx - hy
    have htarget : 2 * medial.2 = 2 * (R.height : ℤ) * w.2 := by
      calc
        _ = 4 * (R.height / 2 : ℕ) * w.2 := htwo
        _ = 2 * (R.height : ℤ) * w.2 := by
          linear_combination 2 * w.2 * hheight
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      (by simpa [mul_assoc] using htarget)


end
end StatMech.FrontierD
