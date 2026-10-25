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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCaccioppoli


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_support
    (m : Nat) : ∀ p,
    fkIsingSquareRadialPatchPrimalInteriorCutoff m p ≠ 0 →
      ¬ fkIsingSquareRadialPatchPrimalBoundary m p := by
  intro p hp hboundary
  simp [fkIsingSquareRadialPatchPrimalInteriorCutoff, hboundary] at hp

theorem fkIsingSquareRadialPatchDualInteriorCutoff_support
    (m : Nat) : ∀ p,
    fkIsingSquareRadialPatchDualInteriorCutoff m p ≠ 0 →
      ¬ fkIsingSquareRadialPatchDualBoundary m p := by
  intro p hp hboundary
  simp [fkIsingSquareRadialPatchDualInteriorCutoff, hboundary] at hp

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz
    (n m : Nat) (hm : m ≤ n)
    (d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart) :
    |fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd -
      fkIsingSquareRadialPatchPrimalInteriorCutoff m d.fst| ≤ 1 := by
  by_cases hs : fkIsingSquareRadialPatchPrimalBoundary m d.snd <;>
    by_cases hf : fkIsingSquareRadialPatchPrimalBoundary m d.fst <;>
    simp [fkIsingSquareRadialPatchPrimalInteriorCutoff, hs, hf]

theorem fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz
    (m : Nat) (d : (fkIsingSquareRadialPatchDualGraph m).Dart) :
    |fkIsingSquareRadialPatchDualInteriorCutoff m d.snd -
      fkIsingSquareRadialPatchDualInteriorCutoff m d.fst| ≤ 1 := by
  by_cases hs : fkIsingSquareRadialPatchDualBoundary m d.snd <;>
    by_cases hf : fkIsingSquareRadialPatchDualBoundary m d.fst <;>
    simp [fkIsingSquareRadialPatchDualInteriorCutoff, hs, hf]

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_one
    (n m : Nat) (hm : m ≤ n) : ∀ d ∈
      fkIsingSquareRadialPatchPrimalInteriorDarts n m hm,
      (1 : Real) ≤ fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd := by
  intro d hd
  have hone : fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd = 1 := by
    simpa [fkIsingSquareRadialPatchPrimalInteriorDarts] using hd
  rw [hone]

theorem fkIsingSquareRadialPatchDualInteriorCutoff_one
    (m : Nat) : ∀ d ∈ fkIsingSquareRadialPatchDualInteriorDarts m,
      (1 : Real) ≤ fkIsingSquareRadialPatchDualInteriorCutoff m d.snd := by
  intro d hd
  have hone : fkIsingSquareRadialPatchDualInteriorCutoff m d.snd = 1 := by
    simpa [fkIsingSquareRadialPatchDualInteriorDarts] using hd
  rw [hone]

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le
    (n m : Nat) (hm : m ≤ n) :
    isingFiniteGraphDartSum
        (fkIsingSquareRadialPatchPrimalGraph n m hm)
        (fun x y ↦
          (fkIsingSquareRadialPatchPrimalInteriorCutoff m y -
            fkIsingSquareRadialPatchPrimalInteriorCutoff m x) ^ 2) ≤
      4 * (m : Real) ^ 2 := by
  have h := isingFiniteGraphDartSum_cutoffEnergy_le
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff m) 4 1
    (fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four n m hm)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz n m hm)
  have hcardNat :
      Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 ≤
        4 * m ^ 2 := by
    calc
      _ ≤ m ^ 2 * 4 := Nat.mul_le_mul_right 4
        (fkIsingSquareRadialPatchPrimalNode_card_le_sq m)
      _ = 4 * m ^ 2 := by ring
  have hcardReal :
      ((Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 : Nat) :
          Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    _ ≤ (Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 : Nat) *
        (1 : Real) ^ 2 := h
    _ = ((Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 : Nat) :
        Real) := by norm_num
    _ ≤ 4 * (m : Real) ^ 2 := hcardReal

theorem fkIsingSquareRadialPatchDualInteriorCutoff_energy_le
    (m : Nat) :
    isingFiniteGraphDartSum
        (fkIsingSquareRadialPatchDualGraph m)
        (fun x y ↦
          (fkIsingSquareRadialPatchDualInteriorCutoff m y -
            fkIsingSquareRadialPatchDualInteriorCutoff m x) ^ 2) ≤
      4 * (m : Real) ^ 2 := by
  have h := isingFiniteGraphDartSum_cutoffEnergy_le
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualInteriorCutoff m) 4 1
    (fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four m)
    (by norm_num)
    (fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz m)
  have hcardNat :
      Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 ≤
        4 * m ^ 2 := by
    calc
      _ ≤ m ^ 2 * 4 := Nat.mul_le_mul_right 4
        (fkIsingSquareRadialPatchDualNode_card_le_sq m)
      _ = 4 * m ^ 2 := by ring
  have hcardReal :
      ((Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 : Nat) :
          Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    _ ≤ (Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 : Nat) *
        (1 : Real) ^ 2 := h
    _ = ((Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 : Nat) :
        Real) := by norm_num
    _ ≤ 4 * (m : Real) ^ 2 := hcardReal


theorem fkIsingSquareRadialPatchPrimitive_mem_range
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    -(2 * (m : Real)) ≤
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ∧
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤
        2 * (m : Real) := by
  have habs := abs_fkIsingSquareRadialPatchPrimitive_le
    n m hn hm hmpos i j
  have hij : (i : Real) + (j : Real) ≤ 2 * (m : Real) := by
    exact_mod_cast (by omega : i + j ≤ 2 * m)
  exact abs_le.mp (habs.trans hij)

theorem fkIsingSquareRadialPatchPrimalValue_mem_range
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) :
    base - 2 * (m : Real) ≤
        fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ∧
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤
        base + 2 * (m : Real) := by
  have h := fkIsingSquareRadialPatchPrimitive_mem_range
    n m hn hm hmpos p.1.1.1 p.1.2.1 p.1.1.2 p.1.2.2
  unfold fkIsingSquareRadialPatchPrimalValue
  constructor <;> linarith

theorem fkIsingSquareRadialPatchDualValue_mem_range
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchDualNode m) :
    base - 2 * (m : Real) ≤
        fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ∧
      fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤
        base + 2 * (m : Real) := by
  have h := fkIsingSquareRadialPatchPrimitive_mem_range
    n m hn hm hmpos p.1.1.1 p.1.2.1 p.1.1.2 p.1.2.2
  unfold fkIsingSquareRadialPatchDualValue
  constructor <;> linarith


theorem fkIsingSquareRadialPatchDual_interiorVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    (∑ d ∈ fkIsingSquareRadialPatchDualInteriorDarts m,
        |fkIsingSquareRadialPatchDualValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      256 * (#(fkIsingSquareRadialPatchDualInteriorDarts m) : Real) *
        (m : Real) ^ 4 := by
  have h := isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualInteriorCutoff m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base)
    (base - 2 * (m : Real)) (base + 2 * (m : Real)) 1
    (4 * (m : Real) ^ 2)
    (fkIsingSquareRadialPatchDualInteriorDarts m)
    (fkIsingSquareRadialPatchDualValue_subharmonicOn
      n m hn hm hmpos base)
    (fun p ↦ (fkIsingSquareRadialPatchDualValue_mem_range
      n m hn hm hmpos base p).1)
    (fun p ↦ (fkIsingSquareRadialPatchDualValue_mem_range
      n m hn hm hmpos base p).2)
    (fkIsingSquareRadialPatchDualInteriorCutoff_support m)
    (by norm_num)
    (fkIsingSquareRadialPatchDualInteriorCutoff_one m)
    (fkIsingSquareRadialPatchDualInteriorCutoff_energy_le m)
  norm_num at h
  ring_nf at h ⊢
  exact h


theorem fkIsingSquareRadialPatchPrimal_interiorVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    (∑ d ∈ fkIsingSquareRadialPatchPrimalInteriorDarts n m hm,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      256 * (#(fkIsingSquareRadialPatchPrimalInteriorDarts n m hm) : Real) *
        (m : Real) ^ 4 := by
  have h := isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff m)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
    (base - 2 * (m : Real)) (base + 2 * (m : Real)) 1
    (4 * (m : Real) ^ 2)
    (fkIsingSquareRadialPatchPrimalInteriorDarts n m hm)
    (fkIsingSquareRadialPatchPrimalValue_superharmonicOn
      n m hn hm hmpos base)
    (fun p ↦ (fkIsingSquareRadialPatchPrimalValue_mem_range
      n m hn hm hmpos base p).1)
    (fun p ↦ (fkIsingSquareRadialPatchPrimalValue_mem_range
      n m hn hm hmpos base p).2)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_support m)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_one n m hm)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le n m hm)
  norm_num at h
  ring_nf at h ⊢
  exact h

end
end StatMech.Universality
