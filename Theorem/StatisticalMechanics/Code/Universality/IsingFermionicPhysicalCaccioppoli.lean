/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveBounds


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four
    (m : Nat) (p : FKIsingSquareRadialPatchDualNode m) :
    Nat.card ((fkIsingSquareRadialPatchDualGraph m).neighborSet p) ≤ 4 := by
  classical
  let code : (fkIsingSquareRadialPatchDualGraph m).neighborSet p →
      Bool × Bool := fun q ↦
    (decide (p.1.1.1 + 1 = q.1.1.1),
      decide (p.1.2.1 + 1 = q.1.1.2.1))
  have hcode : Function.Injective code := by
    intro q r hqr
    have hq := q.2
    have hr := r.2
    change
      (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
        (p.1.2.1 + 1 = q.1.1.2.1 ∨ q.1.1.2.1 + 1 = p.1.2.1) at hq
    change
      (p.1.1.1 + 1 = r.1.1.1 ∨ r.1.1.1 + 1 = p.1.1.1) ∧
        (p.1.2.1 + 1 = r.1.1.2.1 ∨ r.1.1.2.1 + 1 = p.1.2.1) at hr
    have hqx := hq.1
    have hqy := hq.2
    have hrx := hr.1
    have hry := hr.2
    have hqr0 := congrArg Prod.fst hqr
    have hqr1 := congrArg Prod.snd hqr
    dsimp [code] at hqr0 hqr1
    have hx : q.1.1.1.1 = r.1.1.1.1 := by
      rcases hqx with hqx | hqx <;> rcases hrx with hrx | hrx
      · omega
      · simp [hqx] at hqr0
        omega
      · simp [hrx] at hqr0
        omega
      · omega
    have hy : q.1.1.2.1 = r.1.1.2.1 := by
      rcases hqy with hqy | hqy <;> rcases hry with hry | hry
      · omega
      · simp [hqy] at hqr1
        omega
      · simp [hry] at hqr1
        omega
      · omega
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Fin.ext hx) (Fin.ext hy)
  have hcard := Fintype.card_le_of_injective code hcode
  norm_num [code] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard


theorem fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four
    (n m : Nat) (hm : m ≤ n)
    (p : FKIsingSquareRadialPatchPrimalNode m) :
    Nat.card ((fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p) ≤
      4 := by
  classical
  let embed := fkIsingSquareRadialPatchPrimalNodeVertex n m hm
  let code :
      (fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p →
        (fkSquareBoxPlanar n).G.neighborSet (embed p) := fun q ↦
    ⟨embed q.1, by
      have hq := q.2
      change (fkSquareBoxPlanar n).G.Adj (embed p) (embed q.1) at hq
      exact hq⟩
  have hcode : Function.Injective code := by
    intro q r hqr
    apply Subtype.ext
    apply fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm
    exact congrArg Subtype.val hqr
  calc
    Nat.card ((fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p) ≤
        Nat.card ((fkSquareBoxPlanar n).G.neighborSet (embed p)) :=
      Nat.card_le_card_of_injective code hcode
    _ = (fkSquareBoxPlanar n).G.degree (embed p) := by
      rw [Nat.card_eq_fintype_card,
        SimpleGraph.card_neighborSet_eq_degree]
    _ ≤ 4 := by
      simpa only [fkSquareBoxPlanar_graph] using
        StatMech.FK.qp_boxGraph_degree_le 2 n (embed p)


end
end StatMech.Universality
