/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part5
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem quantumIsingSpaceTimeBlockEquiv_apply
    (n k L : Nat) (omega : Fin n -> QuantumIsingChainConfig (k * L))
    (t : Fin n) (b : Fin k) (i : Fin L) :
    quantumIsingSpaceTimeBlockEquiv n k L omega t b i =
      omega t (finProdFinEquiv (b, i)) := by
  rfl

@[simp] theorem quantumIsingSpaceTimeBlockEquiv_symm_apply
    (n k L : Nat) (omega : QuantumIsingSpaceTimeBlockConfig n k L)
    (t : Fin n) (b : Fin k) (i : Fin L) :
    (quantumIsingSpaceTimeBlockEquiv n k L).symm omega t
        (finProdFinEquiv (b, i)) = omega t b i := by
  simp [quantumIsingSpaceTimeBlockEquiv]


theorem quantumIsingClassicalCylinderWeight_blockEquiv
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) :
    quantumIsingClassicalCylinderWeight beta h n
        ((k + 1) * (L + 1))
        ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega) =
      quantumIsingBlockLongCylinderWeight beta h n k L omega := by
  unfold quantumIsingClassicalCylinderWeight
  unfold quantumIsingBlockLongCylinderWeight
  apply Finset.prod_congr rfl
  intro t _
  unfold quantumIsingSpatialTrotterWeight
  rw [show quantumIsingChainInteraction ((k + 1) * (L + 1))
      ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega t) =
        quantumIsingBlockLongInteraction k L (omega t) by rfl]
  congr 1
  unfold quantumIsingBlockVerticalLayerWeight
  calc
      (∏ i : Fin ((k + 1) * (L + 1)),
        quantumIsingVerticalBondWeight beta h n
          ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega t i)
          ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega
            (quantumIsingCyclicSucc t) i)) =
        ∏ p : Fin (k + 1) × Fin (L + 1),
          quantumIsingVerticalBondWeight beta h n
            ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega t
              (finProdFinEquiv p))
            ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega
              (quantumIsingCyclicSucc t) (finProdFinEquiv p)) := by
        exact (Equiv.prod_comp finProdFinEquiv _).symm
      _ = ∏ b : Fin (k + 1), ∏ i : Fin (L + 1),
          quantumIsingVerticalBondWeight beta h n
            (omega t b i) (omega (quantumIsingCyclicSucc t) b i) := by
        rw [Fintype.prod_prod_type]
        simp


theorem quantumIsingBlockPeriodicCylinderWeight_eq_prod
    (beta h : Real) (n k L : Nat)
    (omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)) :
    quantumIsingBlockPeriodicCylinderWeight beta h n k L omega =
      ∏ b : Fin (k + 1),
        quantumIsingClassicalCylinderWeight beta h n (L + 1)
          (fun t => omega t b) := by
  unfold quantumIsingBlockPeriodicCylinderWeight
  calc
    (∏ t : Fin n,
      Real.exp (beta / (4 * n) *
        quantumIsingBlockPeriodicInteraction k L (omega t)) *
        quantumIsingBlockVerticalLayerWeight beta h n (k + 1) (L + 1) omega t) =
      ∏ t : Fin n, ∏ b : Fin (k + 1),
        quantumIsingSpatialTrotterWeight beta n (L + 1) (omega t b) *
          (∏ i : Fin (L + 1),
            quantumIsingVerticalBondWeight beta h n
              (omega t b i) (omega (quantumIsingCyclicSucc t) b i)) := by
      apply Finset.prod_congr rfl
      intro t _
      unfold quantumIsingBlockPeriodicInteraction
      unfold quantumIsingBlockVerticalLayerWeight
      have hexp : Real.exp (beta / (4 * (n : Real)) *
            ∑ b : Fin (k + 1), quantumIsingChainInteraction (L + 1) (omega t b)) =
          ∏ b : Fin (k + 1),
            Real.exp (beta / (4 * (n : Real)) *
              quantumIsingChainInteraction (L + 1) (omega t b)) := by
        rw [Finset.mul_sum]
        exact Real.exp_sum Finset.univ _
      rw [hexp, Finset.prod_mul_distrib]
      rfl
    _ = ∏ b : Fin (k + 1), ∏ t : Fin n,
        quantumIsingSpatialTrotterWeight beta n (L + 1) (omega t b) *
          (∏ i : Fin (L + 1),
            quantumIsingVerticalBondWeight beta h n
              (omega t b i) (omega (quantumIsingCyclicSucc t) b i)) := by
      rw [← Fintype.prod_prod_type']
      exact Fintype.prod_prod_type_right'
        (γ := Real) (α₁ := Fin n) (α₂ := Fin (k + 1))
        (fun t b =>
          quantumIsingSpatialTrotterWeight beta n (L + 1) (omega t b) *
            ∏ i : Fin (L + 1),
              quantumIsingVerticalBondWeight beta h n
                (omega t b i) (omega (quantumIsingCyclicSucc t) b i))
    _ = ∏ b : Fin (k + 1),
        quantumIsingClassicalCylinderWeight beta h n (L + 1)
          (fun t => omega t b) := by
      rfl

end StatMech.FrontierA
