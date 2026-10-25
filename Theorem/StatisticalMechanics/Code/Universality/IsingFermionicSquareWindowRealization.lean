/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalAverageAnchor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part3


namespace StatMech.Universality

open Finset

noncomputable section

theorem fkIsingSquareRadialPatchEdge_injective
    (n m : Nat) (hm : m ≤ n) :
    Function.Injective
      (fun p : Fin m × Fin m ↦
        fkIsingSquareRadialPatchEdge n m hm p.1 p.2) := by
  intro p q hpq
  let up := fkIsingSquareRadialPatchVertex n m hm p.1 p.2
  let uq := fkIsingSquareRadialPatchVertex n m hm q.1 q.2
  let dp := fkIsingSquareRadialPatchDirection p.1.1 p.2.1
  let dq := fkIsingSquareRadialPatchDirection q.1.1 q.2.1
  let vp := fkIsingSquareNeighbor n up dp
    (fkIsingSquareRadialPatchDirection_available n m hm p.1 p.2)
  let vq := fkIsingSquareNeighbor n uq dq
    (fkIsingSquareRadialPatchDirection_available n m hm q.1 q.2)
  have hs : s(up, vp) = s(uq, vq) := by
    exact congrArg Subtype.val hpq
  rcases Sym2.eq_iff.mp hs with hsame | hswap
  · have hx : up.1 0 + vp.1 0 = uq.1 0 + vq.1 0 := by
      rw [hsame.1, hsame.2]
    have hy : up.1 1 + vp.1 1 = uq.1 1 + vq.1 1 := by
      rw [hsame.1, hsame.2]
    by_cases hp : Even (p.1.1 + p.2.1) <;>
      by_cases hq : Even (q.1.1 + q.2.1)
    all_goals
      have hpmod := hp
      have hqmod := hq
      simp only [Nat.even_iff] at hpmod hqmod
      have hpcoord :
          2 * ((p.1.1 + p.2.1 + 1) / 2) =
            if Even (p.1.1 + p.2.1) then p.1.1 + p.2.1
            else p.1.1 + p.2.1 + 1 := by
        simp [hp]
        omega
      have hqcoord :
          2 * ((q.1.1 + q.2.1 + 1) / 2) =
            if Even (q.1.1 + q.2.1) then q.1.1 + q.2.1
            else q.1.1 + q.2.1 + 1 := by
        simp [hq]
        omega
      simp [hp, hq] at hpcoord hqcoord
      simp [up, uq, vp, vq, dp, dq, fkIsingSquareRadialPatchDirection,
        hp, hq, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareRadialPatchVertex] at hx hy
      simp_rw [fkIsingSquareRadialPatchHalf_eq] at hx hy
    all_goals
      apply Prod.ext <;> apply Fin.ext <;> omega
  · have hx : up.1 0 + vp.1 0 = uq.1 0 + vq.1 0 := by
      rw [hswap.1, hswap.2]
      ring
    have hy : up.1 1 + vp.1 1 = uq.1 1 + vq.1 1 := by
      rw [hswap.1, hswap.2]
      ring
    by_cases hp : Even (p.1.1 + p.2.1) <;>
      by_cases hq : Even (q.1.1 + q.2.1)
    all_goals
      have hpmod := hp
      have hqmod := hq
      simp only [Nat.even_iff] at hpmod hqmod
      have hpcoord :
          2 * ((p.1.1 + p.2.1 + 1) / 2) =
            if Even (p.1.1 + p.2.1) then p.1.1 + p.2.1
            else p.1.1 + p.2.1 + 1 := by
        simp [hp]
        omega
      have hqcoord :
          2 * ((q.1.1 + q.2.1 + 1) / 2) =
            if Even (q.1.1 + q.2.1) then q.1.1 + q.2.1
            else q.1.1 + q.2.1 + 1 := by
        simp [hq]
        omega
      simp [hp, hq] at hpcoord hqcoord
      simp [up, uq, vp, vq, dp, dq, fkIsingSquareRadialPatchDirection,
        hp, hq, fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareRadialPatchVertex] at hx hy
      simp_rw [fkIsingSquareRadialPatchHalf_eq] at hx hy
    all_goals
      apply Prod.ext <;> apply Fin.ext <;> omega


end
end StatMech.Universality
