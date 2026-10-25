/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem isingLineCenteredSq_step
    (m : Nat) (p : IsingLineBox (2 * m))
    (hp : ¬ isingLineBoxBoundary (2 * m) p) :
    isingLineCenteredSq m (isingLineWest (2 * m) p) +
        isingLineCenteredSq m (isingLineEast (2 * m) p hp) =
      2 * isingLineCenteredSq m p + 2 := by
  unfold isingLineCenteredSq isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < 2 * m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring

theorem isingLineStoppedMean_centeredSq_le
    (m t : Nat) (p : IsingLineBox (2 * m)) :
    isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) p ≤
      isingLineCenteredSq m p + (t : Real) := by
  induction t generalizing p with
  | zero =>
      simp [isingLineStoppedMean, isingLineStoppedKernel]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary (2 * m) p
      · rw [dif_pos hp]
        have h := ih p
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith
      · rw [dif_neg hp]
        have hw := ih (isingLineWest (2 * m) p)
        have he := ih (isingLineEast (2 * m) p hp)
        have hs := isingLineCenteredSq_step m p hp
        norm_num [Nat.cast_add, Nat.cast_one]
        linarith


theorem isingLineStoppedKernel_center_boundary_le
    (m t : Nat) (hm : 0 < m) :
    isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨2 * m, by omega⟩ ≤
      (t : Real) / (m : Real) ^ 2 := by
  have hmean := isingLineStoppedMean_centeredSq_le m t
    (⟨m, by omega⟩ : IsingLineBox (2 * m))
  have hmReal : 0 < (m : Real) ^ 2 := by positivity
  apply (le_div_iff₀ hmReal).2
  let center : IsingLineBox (2 * m) := ⟨m, by omega⟩
  let left : IsingLineBox (2 * m) := ⟨0, by omega⟩
  let right : IsingLineBox (2 * m) := ⟨2 * m, by omega⟩
  have hlr : left ≠ right := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [left, right] at hv
    omega
  have hboundary :
      (m : Real) ^ 2 *
          (isingLineStoppedKernel (2 * m) t center left +
            isingLineStoppedKernel (2 * m) t center right) ≤
        isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) center := by
    calc
      _ = isingLineStoppedKernel (2 * m) t center left *
            isingLineCenteredSq m left +
          isingLineStoppedKernel (2 * m) t center right *
            isingLineCenteredSq m right := by
        simp [isingLineCenteredSq, left, right]
        ring
      _ = ∑ q ∈ {left, right},
          isingLineStoppedKernel (2 * m) t center q *
            isingLineCenteredSq m q := by
        rw [Finset.sum_pair hlr]
      _ ≤ ∑ q, isingLineStoppedKernel (2 * m) t center q *
          isingLineCenteredSq m q := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro q
        exact mul_nonneg (isingLineStoppedKernel_nonneg _ _ _ _)
          (sq_nonneg _)
      _ = _ := rfl
  have hmean' :
      isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) center ≤
        (t : Real) := by
    simpa [center, isingLineCenteredSq] using hmean
  change (isingLineStoppedKernel (2 * m) t center left +
      isingLineStoppedKernel (2 * m) t center right) * (m : Real) ^ 2 ≤
        (t : Real)
  calc
    _ = (m : Real) ^ 2 *
        (isingLineStoppedKernel (2 * m) t center left +
          isingLineStoppedKernel (2 * m) t center right) := by ring
    _ ≤ isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) center :=
      hboundary
    _ ≤ (t : Real) := hmean' 


theorem isingLineChoiceRun_append (n : Nat) (p : IsingLineBox n)
    (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

theorem isingLineChoiceRun_of_boundary
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun, isingLeapfrogChoiceNext]
      rw [show isingLineChoiceNext n p b = p by simp [isingLineChoiceNext, hp]]
      exact ih


end
end StatMech.Universality
