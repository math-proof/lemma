/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Def.StatisticalMechanics.Code.Walls.bc40funnel.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc40_chainShadow_universalFunnel_false :
    ¬ ∀ (b : Fin 6 → Fin 6),
        b = ![3, 4, 5, 3, 4, 5] →
        ∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) →
          ∀ x : Fin 6, x ≠ s → x ≠ t →
            bc40_chainLab t (b x) = bc40_chainLab t s := by
  intro h
  have h40 : (4 : Fin 6) ≠ 0 := by decide
  have h41 : (4 : Fin 6) ≠ 1 := by decide
  have hkey := h ![3, 4, 5, 3, 4, 5] rfl 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) 4 h40 h41
  
  have hb : (![3, 4, 5, 3, 4, 5] : Fin 6 → Fin 6) 4 = 4 := by
    simp [Matrix.cons_val, Fin.isValue]
  have hL1 : bc40_chainLab 1 4 = 104 := by simp [bc40_chainLab]
  have hL2 : bc40_chainLab 1 0 = 2 := by simp [bc40_chainLab]
  rw [hb, hL1, hL2] at hkey
  exact absurd hkey (by norm_num)


theorem bc40_chainShadow_allTrifFunnel_false :
    ¬ ∀ (b : Fin 6 → Fin 6),
        b = ![3, 4, 5, 3, 4, 5] →
        ∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) →
          ∀ x : Fin 6, (x = 0 ∨ x = 1 ∨ x = 2) → x ≠ s → x ≠ t →
            bc40_chainLab t (b x) = bc40_chainLab t s := by
  intro h
  have h20 : (2 : Fin 6) ≠ 0 := by decide
  have h21 : (2 : Fin 6) ≠ 1 := by decide
  have hkey := h ![3, 4, 5, 3, 4, 5] rfl 1 0 (Or.inr (Or.inl ⟨rfl, rfl⟩)) 2
    (Or.inr (Or.inr rfl)) h20 h21
  
  have hb : (![3, 4, 5, 3, 4, 5] : Fin 6 → Fin 6) 2 = 5 := by
    simp [Matrix.cons_val, Fin.isValue]
  have hL1 : bc40_chainLab 1 5 = 3 := by simp [bc40_chainLab]
  have hL2 : bc40_chainLab 1 0 = 2 := by simp [bc40_chainLab]
  rw [hb, hL1, hL2] at hkey
  exact absurd hkey (by norm_num)


theorem bc40_chainShadow_consistent :
    ∃ (b : Fin 6 → Fin 6) (Rc : Fin 6 → Fin 6 → Fin 6 → Prop),
      (∀ c u v, Rc c u v ↔ bc40_chainLab c u = bc40_chainLab c v) ∧
      (∀ t s : Fin 6, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) →
        (¬ Rc t (b t) (b s)) ∧
        (¬ Rc t (b t) s) ∧
        (∀ x : Fin 6, x ≠ t → Rc t x s → Rc t (b x) s)) := by
  refine ⟨![3, 4, 5, 3, 4, 5], (fun c u v => bc40_chainLab c u = bc40_chainLab c v),
    fun _ _ _ => Iff.rfl, ?_⟩
  decide


theorem bc40_rootSideComparable_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc40_RootSideComparable ω n rank par := by
  intro x hxbox htri; exact absurd htri (hno x hxbox)


end StatMech.Walls
