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
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem tanh_quantumIsingSquareTorusCoupling
    (beta h : Real) (L : Nat) :
    (fun edge ↦ Real.tanh (quantumIsingSquareTorusCoupling beta h L edge)) =
      quantumIsingSquareTorusTanhWeight beta h L := by
  funext edge
  unfold quantumIsingSquareTorusCoupling quantumIsingSquareTorusTanhWeight
  split <;> rfl

theorem coe_quantumIsingSquareTorusTanhWeight
    (beta h : Real) (L : Nat) :
    (fun edge ↦ (quantumIsingSquareTorusTanhWeight beta h L edge : Complex)) =
      anisotropicSquareEdgeWeight L
        (Real.tanh (beta / (4 * L)))
        (Real.tanh (quantumIsingVerticalCoupling beta h L)) := by
  funext edge
  unfold quantumIsingSquareTorusTanhWeight anisotropicSquareEdgeWeight
  split <;> rfl

theorem prod_cosh_quantumIsingSquareTorusCoupling
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    (∏ edge ∈ (onsTorusGraph L).edgeFinset,
        Real.cosh (quantumIsingSquareTorusCoupling beta h L edge)) =
      (Real.cosh (beta / (4 * L)) *
        Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) := by
  rw [prod_squareTorus_edges_eq_positive_directions]
  simp only [quantumIsingSquareTorusCoupling_horizontal,
    quantumIsingSquareTorusCoupling_vertical, Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, ZMod.card]


theorem quantumIsingClassicalCylinderPartition_highTemperature
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    quantumIsingClassicalCylinderPartition beta h L L =
      (2 : Real) ^ (L * L) *
        (Real.cosh (beta / (4 * L)) *
          Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) *
        inhomogeneousEvenSubgraphSum (onsTorusGraph L)
          (quantumIsingSquareTorusTanhWeight beta h L) := by
  rw [quantumIsingClassicalCylinderPartition_eq_torus_ZJ,
    inhomogeneousIsingPartition_highTemperature,
    prod_cosh_quantumIsingSquareTorusCoupling,
    tanh_quantumIsingSquareTorusCoupling]
  congr 3
  simp only [Fintype.card_prod, ZMod.card]


theorem two_mul_quantumIsingClassicalCylinderPartition_eq_spin
    (beta h : Real) (L : Nat) [Fact (2 < L)] :
    (2 : Complex) *
        quantumIsingClassicalCylinderPartition beta h L L =
      ((2 : Real) ^ (L * L) *
          (Real.cosh (beta / (4 * L)) *
            Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) :
        Real) *
        (ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 1 +
          ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 1 +
          ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 0 -
          ons_weightedSpinCharacterSum L
            (anisotropicSquareEdgeWeight L
              (Real.tanh (beta / (4 * L)))
              (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 0) := by
  let prefactor : Real :=
    (2 : Real) ^ (L * L) *
      (Real.cosh (beta / (4 * L)) *
        Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L)
  let evenSum : Real := inhomogeneousEvenSubgraphSum (onsTorusGraph L)
    (quantumIsingSquareTorusTanhWeight beta h L)
  have hpartition :
      quantumIsingClassicalCylinderPartition beta h L L =
        prefactor * evenSum := by
    exact quantumIsingClassicalCylinderPartition_highTemperature beta h L
  have harf := two_mul_inhomogeneousEvenSubgraphSum_eq_spin L
    (quantumIsingSquareTorusTanhWeight beta h L)
  rw [coe_quantumIsingSquareTorusTanhWeight] at harf
  rw [hpartition]
  calc
    (2 : Complex) * ((prefactor * evenSum : Real) : Complex) =
        (prefactor : Complex) * ((2 : Complex) * (evenSum : Complex)) := by
      push_cast
      ring
    _ = (prefactor : Complex) * _ := by rw [harf]

end StatMech.FrontierA
