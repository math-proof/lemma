/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem quantumIsingSquareTorus_energy_eq
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (omega : Fin L → QuantumIsingChainConfig L) :
    (∑ edge ∈ (onsTorusGraph L).edgeFinset,
      quantumIsingSquareTorusCoupling beta h L edge *
        bond (quantumIsingSquareConfigEquiv L omega) edge) =
      quantumIsingSquareTrotterEnergy beta h L omega := by
  rw [sum_squareTorus_edges_eq_positive_directions]
  rw [sum_zmod_square_eq_fin_square]
  simp only [quantumIsingSquareTorusCoupling_horizontal,
    quantumIsingSquareTorusCoupling_vertical]
  simp only [ons_portEdge, ons_dirStep, bond_mk]
  simp_rw [← finEquiv_quantumIsingCyclicSucc]
  unfold spin
  simp only [quantumIsingSquareConfigEquiv_apply]
  unfold quantumIsingSquareTrotterEnergy quantumIsingChainInteraction
    quantumIsingSpinSign
  calc
    (∑ k : Fin L, ∑ i : Fin L,
        (beta / (4 * (L : Real)) *
            ((if omega k i = true then 1 else -1) *
              if omega k (quantumIsingCyclicSucc i) = true then 1 else -1) +
          quantumIsingVerticalCoupling beta h L *
            ((if omega k i = true then 1 else -1) *
              if omega (quantumIsingCyclicSucc k) i = true then 1 else -1))) =
        (∑ k : Fin L, ∑ i : Fin L,
          beta / (4 * (L : Real)) *
            ((if omega k i = true then 1 else -1) *
              if omega k (quantumIsingCyclicSucc i) = true then 1 else -1)) +
        ∑ k : Fin L, ∑ i : Fin L,
          quantumIsingVerticalCoupling beta h L *
            ((if omega k i = true then 1 else -1) *
              if omega (quantumIsingCyclicSucc k) i = true then 1 else -1) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]


theorem quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy
    (beta h : Real) (L : Nat)
    (omega : Fin L → QuantumIsingChainConfig L) :
    quantumIsingClassicalCylinderWeight beta h L L omega =
      Real.exp (quantumIsingSquareTrotterEnergy beta h L omega) := by
  unfold quantumIsingClassicalCylinderWeight
    quantumIsingSpatialTrotterWeight quantumIsingVerticalBondWeight
  simp_rw [← Real.exp_sum, ← Real.exp_add]
  rw [← Real.exp_sum]
  apply congrArg Real.exp
  unfold quantumIsingSquareTrotterEnergy
  rw [Finset.sum_add_distrib]


theorem quantumIsingClassicalCylinderWeight_eq_torus_wJ
    (beta h : Real) (L : Nat) [Fact (2 < L)]
    (omega : Fin L → QuantumIsingChainConfig L) :
    quantumIsingClassicalCylinderWeight beta h L L omega =
      StatMech.Sharpness.wJ (onsTorusGraph L).edgeFinset
        (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0)
        (quantumIsingSquareConfigEquiv L omega) := by
  rw [quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy]
  unfold StatMech.Sharpness.wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [quantumIsingSquareTorus_energy_eq]


theorem quantumIsingClassicalCylinderPartition_eq_torus_ZJ
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    quantumIsingClassicalCylinderPartition beta h L L =
      StatMech.Sharpness.ZJ (onsTorusGraph L).edgeFinset
        (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0) := by
  unfold quantumIsingClassicalCylinderPartition StatMech.Sharpness.ZJ
  rw [← Equiv.sum_comp (quantumIsingSquareConfigEquiv L)
    (StatMech.Sharpness.wJ (onsTorusGraph L).edgeFinset
      (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0))]
  apply Finset.sum_congr rfl
  intro omega _
  exact quantumIsingClassicalCylinderWeight_eq_torus_wJ beta h L omega

end StatMech.FrontierA
