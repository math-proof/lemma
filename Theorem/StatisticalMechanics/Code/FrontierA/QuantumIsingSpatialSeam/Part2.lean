/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part2
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsing_prod_spatial_add
    (L M : Nat) (f : Fin (L + M + 2) -> Real) :
    (∏ i : Fin (L + M + 2), f i) =
      (∏ i : Fin (L + 1), f ⟨i.val, by omega⟩) *
        ∏ j : Fin (M + 1), f ⟨L + 1 + j.val, by omega⟩ := by
  let e := quantumIsingSpatialSumEquiv L M
  calc
    (∏ i : Fin (L + M + 2), f i) =
        ∏ x : Fin (L + 1) ⊕ Fin (M + 1), f (e x) := by
      apply Fintype.prod_equiv e.symm
      intro i
      simp
    _ = (∏ i : Fin (L + 1), f (e (Sum.inl i))) *
          ∏ j : Fin (M + 1), f (e (Sum.inr j)) :=
      Fintype.prod_sum_type _
    _ = _ := by
      apply congrArg₂ (fun x y : Real => x * y)
      · apply Finset.prod_congr rfl
        intro i _
        congr 1
      · apply Finset.prod_congr rfl
        intro j _
        congr 1

theorem quantumIsingCyclicSucc_castSucc {L : Nat} (i : Fin L) :
    quantumIsingCyclicSucc (i.castSucc : Fin (L + 1)) = i.succ := by
  apply Fin.ext
  simp only [quantumIsingCyclicSucc, Fin.val_castSucc, Fin.val_succ]
  rw [Nat.mod_eq_of_lt]
  omega

theorem quantumIsingCyclicSucc_last (L : Nat) :
    quantumIsingCyclicSucc (Fin.last L) = (0 : Fin (L + 1)) := by
  apply Fin.ext
  simp [quantumIsingCyclicSucc]


theorem quantumIsingChainInteraction_succ_eq_open_add_seam
    (L : Nat) (sigma : QuantumIsingChainConfig (L + 1)) :
    quantumIsingChainInteraction (L + 1) sigma =
      quantumIsingOpenChainInteraction L sigma +
        quantumIsingSpinSign (sigma (Fin.last L)) *
          quantumIsingSpinSign (sigma 0) := by
  unfold quantumIsingChainInteraction quantumIsingOpenChainInteraction
  rw [Fin.sum_univ_castSucc]
  simp_rw [quantumIsingCyclicSucc_castSucc]
  rw [quantumIsingCyclicSucc_last]


theorem quantumIsingOpenChainInteraction_add
    (L M : Nat) (sigma : QuantumIsingChainConfig (L + M + 2)) :
    quantumIsingOpenChainInteraction (L + M + 1) sigma =
      quantumIsingOpenChainInteraction L
          (quantumIsingLeftSpatialBlock L M sigma) +
        quantumIsingSpinSign
            ((quantumIsingLeftSpatialBlock L M sigma) (Fin.last L)) *
          quantumIsingSpinSign
            ((quantumIsingRightSpatialBlock L M sigma) 0) +
        quantumIsingOpenChainInteraction M
          (quantumIsingRightSpatialBlock L M sigma) := by
  unfold quantumIsingOpenChainInteraction
  change (∑ i : Fin (L + (M + 1)), _) = _
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_succ]
  have hleft0 (i : Fin L) :
      (Fin.castAdd (M + 1) i : Fin (L + (M + 1))).castSucc =
        (⟨i.val, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    rfl
  have hleft1 (i : Fin L) :
      (Fin.castAdd (M + 1) i : Fin (L + (M + 1))).succ =
        (⟨i.val + 1, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    rfl
  have hcross0 :
      (Fin.natAdd L (0 : Fin (M + 1)) : Fin (L + (M + 1))).castSucc =
        (⟨L, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp
  have hcross1 :
      (Fin.natAdd L (0 : Fin (M + 1)) : Fin (L + (M + 1))).succ =
        (⟨L + 1, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp
  have hright0 (j : Fin M) :
      (Fin.natAdd L j.succ : Fin (L + (M + 1))).castSucc =
        (⟨L + 1 + j.val, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_natAdd, Fin.val_succ]
    omega
  have hright1 (j : Fin M) :
      (Fin.natAdd L j.succ : Fin (L + (M + 1))).succ =
        (⟨L + 2 + j.val, by omega⟩ : Fin (L + M + 2)) := by
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_succ]
    omega
  simp_rw [hleft0, hleft1, hcross0, hcross1, hright0, hright1]
  simp only [quantumIsingLeftSpatialBlock, quantumIsingRightSpatialBlock,
    Fin.val_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
  ring

theorem quantumIsingSpinSign_mul_abs
    (s t : Bool) : |quantumIsingSpinSign s * quantumIsingSpinSign t| = 1 := by
  cases s <;> cases t <;> norm_num [quantumIsingSpinSign]


theorem abs_quantumIsingChainInteraction_sub_open
    (L : Nat) (sigma : QuantumIsingChainConfig (L + 1)) :
    |quantumIsingChainInteraction (L + 1) sigma -
      quantumIsingOpenChainInteraction L sigma| = 1 := by
  rw [quantumIsingChainInteraction_succ_eq_open_add_seam]
  ring_nf
  exact quantumIsingSpinSign_mul_abs _ _


end StatMech.FrontierA
