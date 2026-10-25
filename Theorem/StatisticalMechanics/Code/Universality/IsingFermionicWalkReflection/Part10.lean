/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part11


namespace StatMech.Universality

@[simp] theorem isingLeapfrogBoxReflectX_involutive (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxReflectX R (isingLeapfrogBoxReflectX R p) = p := by
  apply Prod.ext
  · apply Fin.ext
    simp [isingLeapfrogBoxReflectX]
    omega
  · rfl

@[simp] theorem isingLeapfrogBoxReflectX_eq_iff (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogBoxReflectX R p = isingLeapfrogBoxReflectX R q ↔ p = q :=
  (Function.Involutive.injective
    (isingLeapfrogBoxReflectX_involutive R)).eq_iff

theorem isingLeapfrogBoxBoundary_reflectX_iff (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxBoundary R (isingLeapfrogBoxReflectX R p) ↔
      isingLeapfrogBoxBoundary R p := by
  unfold isingLeapfrogBoxBoundary isingLeapfrogBoxReflectX
  dsimp
  omega

theorem isingLeapfrogBoxReflectX_SW (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogSW R p) =
      isingLeapfrogSE R (isingLeapfrogBoxReflectX R p)
        (mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogSouth]

theorem isingLeapfrogBoxReflectX_SE (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogSE R p hp) =
      isingLeapfrogSW R (isingLeapfrogBoxReflectX R p) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogSouth]

theorem isingLeapfrogBoxReflectX_NW (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogNW R p hp) =
      isingLeapfrogNE R (isingLeapfrogBoxReflectX R p)
        (mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogNorth]

theorem isingLeapfrogBoxReflectX_NE (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogNE R p hp) =
      isingLeapfrogNW R (isingLeapfrogBoxReflectX R p)
        (mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogNorth]


theorem isingLeapfrogKilledPathCount_reflectX (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledPathCount R t (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogKilledPathCount R t p q := by
  induction t generalizing p with
  | zero =>
      simp only [isingLeapfrogKilledPathCount]
      rw [if_congr (isingLeapfrogBoxBoundary_reflectX_iff R q) rfl rfl]
      simp
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · have hqr := (isingLeapfrogBoxBoundary_reflectX_iff R q).2 hq
        simp [isingLeapfrogKilledPathCount, hq, hqr]
      · have hqr : ¬ isingLeapfrogBoxBoundary R
            (isingLeapfrogBoxReflectX R q) :=
          mt (isingLeapfrogBoxBoundary_reflectX_iff R q).mp hq
        by_cases hp : isingLeapfrogBoxBoundary R p
        · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
          simp [isingLeapfrogKilledPathCount, hq, hqr, hp, hpr, ih]
        · have hpr : ¬ isingLeapfrogBoxBoundary R
              (isingLeapfrogBoxReflectX R p) :=
            mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
          simp only [isingLeapfrogKilledPathCount, hq, hqr,
            dif_neg hp, dif_neg hpr]
          rw [← isingLeapfrogBoxReflectX_SE R p hp,
            ← isingLeapfrogBoxReflectX_SW R p hp,
            ← isingLeapfrogBoxReflectX_NE R p hp,
            ← isingLeapfrogBoxReflectX_NW R p hp]
          rw [ih, ih, ih, ih]
          simp [add_comm, add_left_comm]

theorem isingLeapfrogStoppedOneStepCount_reflectX (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedOneStepCount R (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogStoppedOneStepCount R p q := by
  by_cases hp : isingLeapfrogBoxBoundary R p
  · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
    simp only [isingLeapfrogStoppedOneStepCount, dif_pos hp, dif_pos hpr]
    simp
  · have hpr : ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogBoxReflectX R p) :=
      mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
    simp only [isingLeapfrogStoppedOneStepCount, dif_neg hp, dif_neg hpr]
    rw [← isingLeapfrogBoxReflectX_SE R p hp,
      ← isingLeapfrogBoxReflectX_SW R p hp,
      ← isingLeapfrogBoxReflectX_NE R p hp,
      ← isingLeapfrogBoxReflectX_NW R p hp]
    simp [add_comm, add_left_comm]


theorem isingLeapfrogFirstHitFluxNumerator_reflectX (R t : Nat)
    (p r q : IsingLeapfrogBox R) :
    isingLeapfrogKilledPathCount R t (isingLeapfrogBoxReflectX R p)
          (isingLeapfrogBoxReflectX R r) *
        isingLeapfrogStoppedOneStepCount R (isingLeapfrogBoxReflectX R r)
          (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogKilledPathCount R t p r *
        isingLeapfrogStoppedOneStepCount R r q := by
  rw [isingLeapfrogKilledPathCount_reflectX,
    isingLeapfrogStoppedOneStepCount_reflectX]


theorem isingLeapfrogFirstHitFluxSummand_reflectX (R t : Nat)
    (p r q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t (isingLeapfrogBoxReflectX R p)
          (isingLeapfrogBoxReflectX R r) *
        isingLeapfrogStoppedKernel R 1 (isingLeapfrogBoxReflectX R r)
          (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q := by
  rw [isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div,
    isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div,
    isingLeapfrogFirstHitFluxNumerator_reflectX]

theorem isingLeapfrogStoppedKernel_reflectX (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogStoppedKernel R t p q := by
  induction t generalizing p with
  | zero => simp [isingLeapfrogStoppedKernel]
  | succ t ih =>
      by_cases hp : isingLeapfrogBoxBoundary R p
      · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
        simp only [isingLeapfrogStoppedKernel, dif_pos hp, dif_pos hpr]
        exact ih p
      · have hpr : ¬ isingLeapfrogBoxBoundary R
            (isingLeapfrogBoxReflectX R p) :=
          mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
        simp only [isingLeapfrogStoppedKernel, dif_neg hp, dif_neg hpr]
        rw [← isingLeapfrogBoxReflectX_SE R p hp,
          ← isingLeapfrogBoxReflectX_SW R p hp,
          ← isingLeapfrogBoxReflectX_NE R p hp,
          ← isingLeapfrogBoxReflectX_NW R p hp]
        rw [ih, ih, ih, ih]
        ring


theorem isingLeapfrogExitKernel_reflectX (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogExitKernel R t (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogExitKernel R t p q := by
  unfold isingLeapfrogExitKernel
  rw [if_congr (isingLeapfrogBoxBoundary_reflectX_iff R q) rfl rfl]
  split_ifs
  · exact isingLeapfrogStoppedKernel_reflectX R t p q
  · rfl


theorem isingLeapfrogDiagonalAdjacent_eq_neighbor {R : Nat}
    (p p' : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    p = isingLeapfrogSW R p' ∨
      p = isingLeapfrogSE R p' hp' ∨
      p = isingLeapfrogNW R p' hp' ∨
      p = isingLeapfrogNE R p' hp' := by
  rcases hpp' with ⟨hx, hy⟩
  unfold Nat.dist at hx hy
  have hx' : p.1.1 + 1 = p'.1.1 ∨ p'.1.1 + 1 = p.1.1 := by omega
  have hy' : p.2.1 + 1 = p'.2.1 ∨ p'.2.1 + 1 = p.2.1 := by omega
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
  · left
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogSW, isingLeapfrogWest]
      omega
    · simp [isingLeapfrogSW, isingLeapfrogSouth]
      omega
  · right; right; left
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogNW, isingLeapfrogWest]
      omega
    · simp [isingLeapfrogNW, isingLeapfrogNorth]
      omega
  · right; left
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogSE, isingLeapfrogEast]
      omega
    · simp [isingLeapfrogSE, isingLeapfrogSouth]
      omega
  · right; right; right
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogNE, isingLeapfrogEast]
      omega
    · simp [isingLeapfrogNE, isingLeapfrogNorth]
      omega


theorem isingLeapfrogExitKernel_neighbor_timeOffset_eq (R t : Nat)
    (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') :
    isingLeapfrogExitKernel R (t + 1) p' q -
        isingLeapfrogExitKernel R t p q =
      ((isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogExitKernel R t p q) +
        (isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogExitKernel R t p q) +
        (isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogExitKernel R t p q) +
        (isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogExitKernel R t p q)) / 4 := by
  rw [isingLeapfrogExitKernel_succ]
  simp only [dif_neg hp']
  ring

theorem isingLeapfrogExitKernel_neighbor_timeOffset_abs_le (R t : Nat)
    (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') :
    |isingLeapfrogExitKernel R (t + 1) p' q -
        isingLeapfrogExitKernel R t p q| ≤
      (|isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogExitKernel R t p q| +
        |isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogExitKernel R t p q| +
        |isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogExitKernel R t p q| +
        |isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogExitKernel R t p q|) / 4 := by
  rw [isingLeapfrogExitKernel_neighbor_timeOffset_eq R t p p' q hp']
  rw [abs_div]
  norm_num
  apply div_le_div_of_nonneg_right _ (by norm_num)
  let a := isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q -
    isingLeapfrogExitKernel R t p q
  let b := isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q -
    isingLeapfrogExitKernel R t p q
  let c := isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q -
    isingLeapfrogExitKernel R t p q
  let d := isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q -
    isingLeapfrogExitKernel R t p q
  change |a + b + c + d| ≤ |a| + |b| + |c| + |d|
  have hab := abs_add_le a b
  have habc := abs_add_le (a + b) c
  have habcd := abs_add_le (a + b + c) d
  linarith


theorem isingLeapfrogStoppedKernel_neighbor_timeOffset_eq (R t : Nat)
    (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') :
    isingLeapfrogStoppedKernel R (t + 1) p' q -
        isingLeapfrogStoppedKernel R t p q =
      ((isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q)) / 4 := by
  rw [isingLeapfrogStoppedKernel_succ]
  simp only [dif_neg hp']
  ring


end StatMech.Universality
