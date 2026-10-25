/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part3


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

@[simp] theorem fkRectBlackOrbitMedialRibbonWord_length
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectBlackOrbitMedialRibbonWord R omega d).length =
      8 * (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  change (l.flatMap fun e =>
    fkRectMedialRibbonBlock (pairing e.1.1) e.1.2).length = 8 * l.length
  induction l with
  | nil => simp
  | cons e tail ih =>
      simp [ih, Nat.mul_add, Nat.add_comm]

theorem fkRectBlackOrbitMedialRibbonWord_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackOrbitMedialRibbonWord R omega d ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  rw [fkRectBlackOrbitMedialRibbonWord_length] at hlen
  simp only [List.length_nil] at hlen
  have hpos := fkRectBlackOrbitList_length_pos
    (fkRectConfigurationToMedialPairing R omega) d
  omega


theorem fkRectBlackOrbitMedialRibbonWord_step_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ((fkRectBlackOrbitMedialRibbonWord R omega d).map stepOf).sum =
      (8 * ((2 * R.width : ℕ) : ℤ) * w.1,
        8 * (R.height : ℤ) * w.2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hn.ne'⟩
  let e : Fin l.length → FKMedialBlackDart R.medialTorus := l.get
  let a : Fin l.length → Int × Int := fun i =>
    stepOf (fkRectBlackBoundaryMedialDirection pairing (e i))
  let p : Fin l.length → Int × Int := fun i =>
    fkRectMedialRibbonPortOffset (e i).1.2
  have hnext (i : Fin l.length) :
      e (i + 1) = fkMedialBlackBoundaryPerm pairing (e i) :=
    fkRectBlackOrbitList_get_add_one pairing d i
  have hblock (i : Fin l.length) :
      ((fkRectMedialRibbonBlock (pairing (e i).1.1) (e i).1.2).map
          stepOf).sum =
        (8 * (a i).1 + (p (i + 1)).1 - (p i).1,
          8 * (a i).2 + (p (i + 1)).2 - (p i).2) := by
    dsimp only [a, p]
    rw [hnext i]
    rcases hdi : e i with ⟨⟨v, side⟩, hd⟩
    cases hp : pairing v <;> cases side <;>
      simp [fkRectMedialRibbonBlock, fkRectMedialRibbonLocalBlock,
        fkRectBlackBoundaryMedialDirection, fkRectMedialSideDirection,
        fkRectMedialRibbonPortOffset, fkMedialBlackBoundaryPerm_val,
        fkRectMedialLocalMateSide, fkMedialLocalMate,
        fkMedialBondMate, hp, stepOf]
  have hpot (coord : (Int × Int) → Int) :
      (∑ i, coord (p (i + 1))) = ∑ i, coord (p i) := by
    change (∑ i, (fun j => coord (p j))
      ((Equiv.addRight (1 : Fin l.length)) i)) = _
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin l.length))
      (fun i => coord (p i))
  have hflat (xs : List (FKMedialBlackDart R.medialTorus)) :
      (((xs.flatMap fun z =>
          fkRectMedialRibbonBlock (pairing z.1.1) z.1.2).map stepOf).sum) =
        (xs.map fun z => ((fkRectMedialRibbonBlock
          (pairing z.1.1) z.1.2).map stepOf).sum).sum := by
    induction xs with
    | nil => simp
    | cons z tail ih =>
        simp [List.sum_append, ih]
  have hsum :
      ((fkRectBlackOrbitMedialRibbonWord R omega d).map stepOf).sum =
        ∑ i, ((fkRectMedialRibbonBlock
          (pairing (e i).1.1) (e i).1.2).map stepOf).sum := by
    rw [show fkRectBlackOrbitMedialRibbonWord R omega d =
      l.flatMap fun z => fkRectMedialRibbonBlock
        (pairing z.1.1) z.1.2 by rfl]
    rw [hflat]
    rw [← List.sum_ofFn]
    let F : FKMedialBlackDart R.medialTorus → Int × Int := fun z =>
      ((fkRectMedialRibbonBlock (pairing z.1.1) z.1.2).map stepOf).sum
    change (l.map F).sum = (List.ofFn fun i => F (l.get i)).sum
    congr 1
    calc
      l.map F = (List.ofFn l.get).map F := by rw [List.ofFn_get]
      _ = List.ofFn (fun i => F (l.get i)) := by
        simp [List.map_ofFn, Function.comp_apply]
  rw [hsum]
  simp_rw [hblock]
  have hmedial := fkRectBlackOrbitMedialDisplacement_eq_winding R omega d
  change ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing (e i)) = _ at hmedial
  rw [ons_pathDisplacement_ofFn] at hmedial
  apply Prod.ext
  · simp only [Prod.fst_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.fst]
    have hx := congrArg Prod.fst hmedial
    simp only [Prod.fst_sum] at hx
    change (∑ i, (a i).1) = _ at hx
    rw [← Finset.mul_sum, hx]
    ring
  · simp only [Prod.snd_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.snd]
    have hy := congrArg Prod.snd hmedial
    simp only [Prod.snd_sum] at hy
    change (∑ i, (a i).2) = _ at hy
    rw [← Finset.mul_sum, hy]
    ring


end
end StatMech.FrontierD
