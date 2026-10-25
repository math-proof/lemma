/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexCoordinateBetheWave_roots
    {N n : Nat} (c : Real) (x : SixVertexSector N n) :
    Continuous (fun p : Fin n -> Real => sixVertexCoordinateBetheWave c p x) := by
  unfold sixVertexCoordinateBetheWave sixVertexBetheAmplitude
    sixVertexBethePairProduct sixVertexBetheMonomial
    sixVertexBethePairFactor sixVertexBethePhase
  fun_prop


theorem sixVertexBethe_intervalLocalSum_one
    (c : Real) {a b : Int} (hab : a < b) :
    (∑ y ∈ Finset.Icc a b,
      (if y = a ∨ y = b then 1 else (c : Complex) ^ 2) *
        (1 : Complex) ^ y) =
      2 + ((b - a - 1).toNat : Complex) * (c : Complex) ^ 2 := by
  have hIcc : Finset.Icc a b =
      insert a (insert b (Finset.Ioo a b)) := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hIcc, Finset.sum_insert, Finset.sum_insert]
  · simp only [true_or, if_true, or_true, one_zpow, mul_one]
    have hinter :
        (∑ y ∈ Finset.Ioo a b,
          if y = a ∨ y = b then 1 else (c : Complex) ^ 2) =
          ((b - a - 1).toNat : Complex) * (c : Complex) ^ 2 := by
      calc
        _ = ∑ _y ∈ Finset.Ioo a b, (c : Complex) ^ 2 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [if_neg]
          exact fun h => by
            rcases h with rfl | rfl <;> simpa using hy
        _ = ((Finset.Ioo a b).card : Complex) * (c : Complex) ^ 2 := by
          simp
        _ = _ := by rw [Int.card_Ioo]
    rw [hinter]
    ring
  · simp
  · simp only [Finset.mem_insert, Finset.mem_Ioo, not_or]
    omega

theorem sixVertexBetheIntervalTupleWeight_factor
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x q : Fin (n + 1) -> Int) :
    sixVertexBetheIntervalTupleWeight N c z x q =
      ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card *
        ∏ i, z i ^ q i := by
  unfold sixVertexBetheIntervalTupleWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  ext i
  simp [sixVertexBetheInteriorSet]


theorem sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) -> Real)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
    sixVertexBetheCollisionConstrainedIntervalSum N c
        (fun i => sixVertexBethePhase (p i)) x S =
      (if ell ∈ S then 1
        else if (finRotate (n + 1)).symm ell ∈ S then 1
        else 2 +
          ((x ell - sixVertexBetheShiftCoordinates N x ell - 1).toNat :
            Complex) * (c : Complex) ^ 2) *
        ∏ i ∈ (Finset.univ.erase ell),
          ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
            (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i
              then 1 else (c : Complex) ^ 2) *
              sixVertexBethePhase (p i) ^ y := by
  let F : Fin (n + 1) -> Complex := fun i =>
    ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
      (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i
        then 1 else (c : Complex) ^ 2) *
        sixVertexBethePhase (p i) ^ y
  rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_prod N c _ x S hS
    (fun i => (hgap i).le)]
  change (∏ i, F i) = _
  rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ ell)]
  congr 1
  by_cases hellS : ell ∈ S
  · simp [F, sixVertexBetheConstrainedCoordinateSet, hellS, hell,
      sixVertexBethePhase]
  · by_cases hpred : (finRotate (n + 1)).symm ell ∈ S
    · have hpred' : ell - 1 ∈ S := by simpa using hpred
      simp [F, sixVertexBetheConstrainedCoordinateSet, hellS, hpred,
        hpred', hell, sixVertexBethePhase]
    · have hpred' : ell - 1 ∉ S := by simpa using hpred
      simp only [F, sixVertexBetheConstrainedCoordinateSet, hellS,
        hpred, hpred', if_false, hell, sixVertexBethePhase,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      exact sixVertexBethe_intervalLocalSum_one c (hgap ell)

theorem sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hS : ¬ SixVertexBetheNoAdjacent S) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S = 0 := by
  classical
  simp only [SixVertexBetheNoAdjacent, not_forall] at hS
  obtain ⟨i, hi⟩ := hS
  simp only [Classical.not_imp, not_not] at hi
  unfold sixVertexBetheCollisionConstrainedIntervalSum
  apply Finset.sum_eq_zero
  intro q hq
  have hsubset := (Finset.mem_filter.mp hq).2
  have hcoli := (mem_sixVertexBetheCollisionSet N x q i).mp
    (hsubset hi.1)
  have hcolnext := (mem_sixVertexBetheCollisionSet N x q
    (finRotate (n + 1) i)).mp (hsubset hi.2)
  exfalso
  exact (hgap (finRotate (n + 1) i)).ne
    (hcoli.2.symm.trans hcolnext.1)

end
end StatMech.FrontierD
