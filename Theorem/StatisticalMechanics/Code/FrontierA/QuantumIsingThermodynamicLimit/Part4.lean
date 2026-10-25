/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part4
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_left
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (i : Fin A) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (finSumFinEquiv (Sum.inl i)) = (omega t).1 i := by
  change (quantumIsingSumBlockEquiv A B).symm (omega t)
    (finSumFinEquiv (Sum.inl i)) = (omega t).1 i
  exact quantumIsingSumBlockEquiv_symm_left A B (omega t) i

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_right
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (j : Fin B) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (finSumFinEquiv (Sum.inr j)) = (omega t).2 j := by
  change (quantumIsingSumBlockEquiv A B).symm (omega t)
    (finSumFinEquiv (Sum.inr j)) = (omega t).2 j
  exact quantumIsingSumBlockEquiv_symm_right A B (omega t) j

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_castAdd
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (i : Fin A) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (Fin.castAdd B i) = (omega t).1 i := by
  change (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
    (finSumFinEquiv (Sum.inl i)) = (omega t).1 i
  exact quantumIsingSpaceTimeSumBlockEquiv_symm_left n A B omega t i

@[simp] theorem quantumIsingSpaceTimeSumBlockEquiv_symm_natAdd
    (n A B : Nat) (omega : QuantumIsingSpaceTimeTwoBlockConfig n A B)
    (t : Fin n) (j : Fin B) :
    (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
        (Fin.natAdd A j) = (omega t).2 j := by
  change (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t
    (finSumFinEquiv (Sum.inr j)) = (omega t).2 j
  exact quantumIsingSpaceTimeSumBlockEquiv_symm_right n A B omega t j

theorem quantumIsingClassicalCylinderWeight_sumBlockEquiv
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) :
    quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1))
        ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega) =
      quantumIsingTwoBlockLongCylinderWeight beta h n A B omega := by
  unfold quantumIsingClassicalCylinderWeight
  unfold quantumIsingTwoBlockLongCylinderWeight
  apply Finset.prod_congr rfl
  intro t _
  unfold quantumIsingSpatialTrotterWeight
  rw [show quantumIsingChainInteraction ((A + 1) + (B + 1))
      ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t) =
        quantumIsingTwoBlockLongInteraction A B (omega t) by rfl]
  congr 1
  unfold quantumIsingTwoBlockVerticalLayerWeight
  calc
    (∏ q : Fin ((A + 1) + (B + 1)),
      quantumIsingVerticalBondWeight beta h n
        ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t q)
        ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega
          (quantumIsingCyclicSucc t) q)) =
      ∏ s : Fin (A + 1) ⊕ Fin (B + 1),
        quantumIsingVerticalBondWeight beta h n
          ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t
            (finSumFinEquiv s))
          ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega
            (quantumIsingCyclicSucc t) (finSumFinEquiv s)) := by
      simpa using (Equiv.prod_comp finSumFinEquiv
        (fun q : Fin ((A + 1) + (B + 1)) =>
          quantumIsingVerticalBondWeight beta h n
            ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega t q)
            ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega
              (quantumIsingCyclicSucc t) q))).symm
    _ = (∏ i : Fin (A + 1), quantumIsingVerticalBondWeight beta h n
          ((omega t).1 i) ((omega (quantumIsingCyclicSucc t)).1 i)) *
        ∏ j : Fin (B + 1), quantumIsingVerticalBondWeight beta h n
          ((omega t).2 j) ((omega (quantumIsingCyclicSucc t)).2 j) := by
      rw [Fintype.prod_sum_type]
      congr 1 <;> apply Finset.prod_congr rfl <;> intro x _ <;> simp

theorem quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul
    (beta h : Real) (n A B : Nat)
    (omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)) :
    quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega =
      quantumIsingClassicalCylinderWeight beta h n (A + 1) (fun t => (omega t).1) *
        quantumIsingClassicalCylinderWeight beta h n (B + 1) (fun t => (omega t).2) := by
  unfold quantumIsingTwoBlockPeriodicCylinderWeight
  unfold quantumIsingClassicalCylinderWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  unfold quantumIsingTwoBlockPeriodicInteraction
  unfold quantumIsingTwoBlockVerticalLayerWeight
  unfold quantumIsingSpatialTrotterWeight
  rw [show beta / (4 * (n : Real)) *
      (quantumIsingChainInteraction (A + 1) (omega t).1 +
        quantumIsingChainInteraction (B + 1) (omega t).2) =
      beta / (4 * (n : Real)) * quantumIsingChainInteraction (A + 1) (omega t).1 +
        beta / (4 * (n : Real)) * quantumIsingChainInteraction (B + 1) (omega t).2 by ring,
    Real.exp_add]
  ring

end StatMech.FrontierA
