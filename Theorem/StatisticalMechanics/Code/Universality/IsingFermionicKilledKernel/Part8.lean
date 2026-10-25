/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part8


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogBoxToPlane_injective {R : Nat} :
    Function.Injective (@isingLeapfrogBoxToPlane R) := by
  intro p q hpq
  unfold isingLeapfrogBoxToPlane at hpq
  have hx : (p.1.1 : Int) = q.1.1 := by
    simpa using congrArg Prod.fst hpq
  have hy : (p.2.1 : Int) = q.2.1 := by
    simpa using congrArg Prod.snd hpq
  apply Prod.ext <;> apply Fin.ext
  · exact_mod_cast hx
  · exact_mod_cast hy

theorem isingLeapfrogBoxToPlane_SW {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogSW R p) =
      isingLeapfrogPlaneSW (isingLeapfrogBoxToPlane p) := by
  have hx : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hy : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  unfold isingLeapfrogBoxToPlane isingLeapfrogSW isingLeapfrogWest
    isingLeapfrogSouth isingLeapfrogPlaneSW
  apply Prod.ext <;> simp <;> omega

theorem isingLeapfrogBoxToPlane_SE {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogSE R p hp) =
      isingLeapfrogPlaneSE (isingLeapfrogBoxToPlane p) := by
  have hy : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  unfold isingLeapfrogBoxToPlane isingLeapfrogSE isingLeapfrogEast
    isingLeapfrogSouth isingLeapfrogPlaneSE
  apply Prod.ext <;> simp <;> omega

theorem isingLeapfrogBoxToPlane_NW {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogNW R p hp) =
      isingLeapfrogPlaneNW (isingLeapfrogBoxToPlane p) := by
  have hx : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  unfold isingLeapfrogBoxToPlane isingLeapfrogNW isingLeapfrogWest
    isingLeapfrogNorth isingLeapfrogPlaneNW
  apply Prod.ext <;> simp <;> omega

theorem isingLeapfrogBoxToPlane_NE {R : Nat}
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxToPlane (isingLeapfrogNE R p hp) =
      isingLeapfrogPlaneNE (isingLeapfrogBoxToPlane p) := by
  unfold isingLeapfrogBoxToPlane isingLeapfrogNE isingLeapfrogEast
    isingLeapfrogNorth isingLeapfrogPlaneNE
  apply Prod.ext <;> simp


theorem isingLeapfrogKilledKernel_le_free (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q ≤
      isingLeapfrogFreeKernel t (isingLeapfrogBoxToPlane p)
        (isingLeapfrogBoxToPlane q) := by
  induction t generalizing p with
  | zero =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · rw [isingLeapfrogKilledKernel]
        simp only [if_pos hq]
        exact isingLeapfrogFreeKernel_nonneg 0 _ _
      · unfold isingLeapfrogKilledKernel
        rw [if_neg hq]
        unfold isingLeapfrogStoppedKernel isingLeapfrogFreeKernel
        by_cases hpq : p = q
        · simp [hpq]
        · simp [hpq, isingLeapfrogBoxToPlane_injective.ne hpq]
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · simp [isingLeapfrogKilledKernel, hq,
          isingLeapfrogFreeKernel_nonneg]
      · by_cases hp : isingLeapfrogBoxBoundary R p
        · rw [isingLeapfrogKilledKernel]
          simp only [if_neg hq]
          rw [isingLeapfrogStoppedKernel_of_boundary R (t + 1) p q hp]
          have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
          simp [hpq, isingLeapfrogFreeKernel_nonneg]
        · rw [isingLeapfrogKilledKernel]
          simp only [if_neg hq, isingLeapfrogStoppedKernel, dif_neg hp,
            isingLeapfrogFreeKernel]
          have hSW := ih (isingLeapfrogSW R p)
          have hSE := ih (isingLeapfrogSE R p hp)
          have hNW := ih (isingLeapfrogNW R p hp)
          have hNE := ih (isingLeapfrogNE R p hp)
          simp only [isingLeapfrogKilledKernel, if_neg hq] at hSW hSE hNW hNE
          rw [isingLeapfrogBoxToPlane_SW p hp] at hSW
          rw [isingLeapfrogBoxToPlane_SE p hp] at hSE
          rw [isingLeapfrogBoxToPlane_NW p hp] at hNW
          rw [isingLeapfrogBoxToPlane_NE p hp] at hNE
          linarith


theorem isingLeapfrogKilledKernel_le (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q ≤ 2 / (t + 1 : Real) := by
  exact le_trans (isingLeapfrogKilledKernel_le_free R t p q)
    (isingLeapfrogFreeKernel_le t _ _)


theorem isingLeapfrogKilledKernel_diffusive_abs_sub_le
    (R ρ : Nat) (p p' q : IsingLeapfrogBox R) (hρ : 0 < ρ) :
    |isingLeapfrogKilledKernel R (ρ * ρ) p q -
        isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q| ≤
      4 / (ρ : Real) ^ 2 := by
  have ha := isingLeapfrogKilledKernel_le R (ρ * ρ) p q
  have hb := isingLeapfrogKilledKernel_le R (ρ * ρ + 1) p' q
  norm_num [Nat.cast_add, Nat.cast_mul] at ha hb
  have hρsq : 0 < (ρ : Real) ^ 2 := by positivity
  have ha' : isingLeapfrogKilledKernel R (ρ * ρ) p q ≤
      2 / (ρ : Real) ^ 2 := by
    refine le_trans ha (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  have hb' : isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q ≤
      2 / (ρ : Real) ^ 2 := by
    refine le_trans hb (div_le_div_of_nonneg_left (by norm_num) hρsq ?_)
    nlinarith
  have ha0 := isingLeapfrogKilledKernel_nonneg R (ρ * ρ) p q
  have hb0 := isingLeapfrogKilledKernel_nonneg R (ρ * ρ + 1) p' q
  have h24 : 2 / (ρ : Real) ^ 2 ≤ 4 / (ρ : Real) ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) hρsq.le
  rw [abs_sub_le_iff]
  constructor <;> linarith


end
end StatMech.Universality
