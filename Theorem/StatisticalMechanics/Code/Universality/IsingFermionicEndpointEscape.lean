/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem isingLineFarFifth_step
    (m : Nat) (p : IsingLineBox m)
    (hp : ¬ isingLineBoxBoundary m p) :
    isingLineFarFifth m (isingLineWest m p) +
        isingLineFarFifth m (isingLineEast m p hp) =
      2 * isingLineFarFifth m p +
        20 * ((m : Real) - (p.1 : Real)) ^ 3 +
          10 * ((m : Real) - (p.1 : Real)) := by
  unfold isingLineFarFifth isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring

theorem isingLineFarThird_step
    (m : Nat) (p : IsingLineBox m)
    (hp : ¬ isingLineBoxBoundary m p) :
    ((m : Real) - ((isingLineWest m p).1 : Real)) ^ 3 +
        ((m : Real) - ((isingLineEast m p hp).1 : Real)) ^ 3 =
      2 * ((m : Real) - (p.1 : Real)) ^ 3 +
        6 * ((m : Real) - (p.1 : Real)) := by
  unfold isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring

theorem isingLineFarFirst_step
    (m : Nat) (p : IsingLineBox m)
    (hp : ¬ isingLineBoxBoundary m p) :
    ((m : Real) - ((isingLineWest m p).1 : Real)) +
        ((m : Real) - ((isingLineEast m p hp).1 : Real)) =
      2 * ((m : Real) - (p.1 : Real)) := by
  unfold isingLineWest isingLineEast
  have hp0 : 0 < p.1 := by
    unfold isingLineBoxBoundary at hp
    omega
  have hpR : p.1 < m := by
    unfold isingLineBoxBoundary at hp
    have hle := p.2
    omega
  push_cast
  rw [Nat.cast_sub hp0]
  ring


theorem isingLineStoppedMean_farFifth_le
    (m t : Nat) (p : IsingLineBox m) :
    isingLineStoppedMean m t (isingLineFarFifth m) p ≤
      ((m : Real) - (p.1 : Real)) ^ 5 +
        10 * (t : Real) * ((m : Real) - (p.1 : Real)) ^ 3 +
          15 * (t : Real) ^ 2 * ((m : Real) - (p.1 : Real)) := by
  induction t generalizing p with
  | zero =>
      simp [isingLineStoppedMean, isingLineStoppedKernel,
        isingLineFarFifth]
  | succ t ih =>
      rw [isingLineStoppedMean_succ]
      by_cases hp : isingLineBoxBoundary m p
      · rw [dif_pos hp]
        have h := ih p
        have hy : 0 ≤ (m : Real) - (p.1 : Real) := by
          have hpLe : p.1 ≤ m := by omega
          have hpLeReal : (p.1 : Real) ≤ (m : Real) := by exact_mod_cast hpLe
          linarith
        have hy3 : 0 ≤ ((m : Real) - (p.1 : Real)) ^ 3 :=
          pow_nonneg hy _
        have hty : 0 ≤ (2 * (t : Real) + 1) *
            ((m : Real) - (p.1 : Real)) :=
          mul_nonneg (by positivity) hy
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith
      · rw [dif_neg hp]
        have hw := ih (isingLineWest m p)
        have he := ih (isingLineEast m p hp)
        have h5 := isingLineFarFifth_step m p hp
        have h3 := isingLineFarThird_step m p hp
        have h1 := isingLineFarFirst_step m p hp
        have hy : 0 ≤ (m : Real) - (p.1 : Real) := by
          have hpLe : p.1 ≤ m := by omega
          have hpLeReal : (p.1 : Real) ≤ (m : Real) := by exact_mod_cast hpLe
          linarith
        unfold isingLineFarFifth at hw he h5 ⊢
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith [sq_nonneg (t : Real)]


theorem isingLineStoppedKernel_far_boundary_le_fifth
    (m t : Nat) (hm : 0 < m) :
    isingLineStoppedKernel m t ⟨m - 1, by omega⟩ ⟨0, by omega⟩ ≤
      26 * (t + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
  have hmean := isingLineStoppedMean_farFifth_le m t
    (⟨m - 1, by omega⟩ : IsingLineBox m)
  have hm5 : 0 < (m : Real) ^ 5 := by positivity
  apply (le_div_iff₀ hm5).2
  let start : IsingLineBox m := ⟨m - 1, by omega⟩
  let far : IsingLineBox m := ⟨0, by omega⟩
  have hboundary :
      (m : Real) ^ 5 * isingLineStoppedKernel m t start far ≤
        isingLineStoppedMean m t (isingLineFarFifth m) start := by
    calc
      _ = isingLineStoppedKernel m t start far *
          isingLineFarFifth m far := by
        simp [isingLineFarFifth, far]
        ring
      _ ≤ ∑ q, isingLineStoppedKernel m t start q *
          isingLineFarFifth m q := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun q : IsingLineBox m =>
            isingLineStoppedKernel m t start q * isingLineFarFifth m q) ?_
          (Finset.mem_univ far)
        intro q hq
        exact mul_nonneg (isingLineStoppedKernel_nonneg _ _ _ _)
          (by
            unfold isingLineFarFifth
            have hqLe : q.1 ≤ m := by omega
            have hqLeReal : (q.1 : Real) ≤ (m : Real) := by exact_mod_cast hqLe
            exact pow_nonneg (sub_nonneg.mpr hqLeReal) _)
      _ = _ := rfl
  have hmean' :
      isingLineStoppedMean m t (isingLineFarFifth m) start ≤
        26 * (t + 1 : Real) ^ 2 := by
    have hcast : ((m - 1 : Nat) : Real) = (m : Real) - 1 := by
      rw [Nat.cast_sub hm]
      norm_num
    dsimp [start] at hmean
    rw [hcast] at hmean
    norm_num at hmean ⊢
    nlinarith [sq_nonneg (t : Real)]
  change isingLineStoppedKernel m t start far * (m : Real) ^ 5 ≤
    26 * (t + 1 : Real) ^ 2
  calc
    _ = (m : Real) ^ 5 * isingLineStoppedKernel m t start far := by ring
    _ ≤ isingLineStoppedMean m t (isingLineFarFifth m) start := hboundary
    _ ≤ 26 * (t + 1 : Real) ^ 2 := hmean'


end
end StatMech.Universality
