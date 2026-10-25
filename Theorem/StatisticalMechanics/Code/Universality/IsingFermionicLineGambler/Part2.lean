/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLineStoppedMean_succ (n t : Nat)
    (f : IsingLineBox n → Real) (p : IsingLineBox n) :
    isingLineStoppedMean n (t + 1) f p =
      if hp : isingLineBoxBoundary n p then
        isingLineStoppedMean n t f p
      else
        (isingLineStoppedMean n t f (isingLineWest n p) +
          isingLineStoppedMean n t f (isingLineEast n p hp)) / 2 := by
  classical
  unfold isingLineStoppedMean
  by_cases hp : isingLineBoxBoundary n p
  · simp [isingLineStoppedKernel, hp]
  · simp only [isingLineStoppedKernel, dif_neg hp]
    calc
      _ = ∑ x, (isingLineStoppedKernel n t (isingLineWest n p) x * f x +
          isingLineStoppedKernel n t (isingLineEast n p hp) x * f x) / 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_add_distrib]

theorem IsingLineHarmonic.stoppedMean_eq {n : Nat}
    {f : IsingLineBox n → Real} (hf : IsingLineHarmonic n f)
    (t : Nat) (p : IsingLineBox n) :
    isingLineStoppedMean n t f p = f p := by
  induction t generalizing p with
  | zero => simp [isingLineStoppedMean, isingLineStoppedKernel]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary n p
      · simp [hp, ih]
      · simp only [dif_neg hp, ih]
        rw [hf p hp]
        ring


theorem isingLineDistanceToRight_harmonic (n : Nat) :
    IsingLineHarmonic n (fun p => (n - p.1 : Nat)) := by
  intro p hp
  unfold isingLineBoxBoundary at hp
  unfold isingLineWest isingLineEast
  change ((n - (p.1 - 1) : Nat) : Real) +
      ((n - (p.1 + 1) : Nat) : Real) =
    2 * ((n - p.1 : Nat) : Real)
  norm_cast
  omega

theorem isingLineStoppedMean_distanceToRight (n t : Nat)
    (p : IsingLineBox n) :
    isingLineStoppedMean n t (fun q => (n - q.1 : Nat)) p =
      (n - p.1 : Nat) :=
  (isingLineDistanceToRight_harmonic n).stoppedMean_eq t p


theorem isingLineStoppedKernel_left_mul_le (n t : Nat)
    (p : IsingLineBox n) :
    (n : Real) * isingLineStoppedKernel n t p ⟨0, by omega⟩ ≤
      (n - p.1 : Nat) := by
  classical
  let left : IsingLineBox n := ⟨0, by omega⟩
  have hterm : (n : Real) * isingLineStoppedKernel n t p left =
      isingLineStoppedKernel n t p left * (n - left.1 : Nat) := by
    simp [left]
    ring
  rw [hterm, ← isingLineStoppedMean_distanceToRight n t p]
  unfold isingLineStoppedMean
  let g : IsingLineBox n → Real := fun q =>
    isingLineStoppedKernel n t p q * (n - q.1 : Nat)
  change g left ≤ ∑ q, g q
  unfold g
  refine Finset.single_le_sum
    (f := fun q : IsingLineBox n =>
      isingLineStoppedKernel n t p q * ((n - q.1 : Nat) : Real)) ?_
    (Finset.mem_univ left)
  intro q hq
  exact mul_nonneg (isingLineStoppedKernel_nonneg n t p q) (by positivity)

theorem isingLineStoppedKernel_left_le (n t : Nat)
    (p : IsingLineBox n) (hn : 0 < n) :
    isingLineStoppedKernel n t p ⟨0, by omega⟩ ≤
      ((n - p.1 : Nat) : Real) / n := by
  apply (le_div_iff₀ (by exact_mod_cast hn)).2
  simpa [mul_comm] using isingLineStoppedKernel_left_mul_le n t p


theorem isingLineStoppedKernel_left_of_rightNeighbor (n t : Nat)
    (hn : 0 < n) :
    isingLineStoppedKernel n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ≤
      1 / (n : Real) := by
  have h := isingLineStoppedKernel_left_le n t
    (⟨n - 1, by omega⟩ : IsingLineBox n) hn
  have hsub : n - (n - 1) = 1 := by omega
  simpa [hsub] using h


end
end StatMech.Universality
