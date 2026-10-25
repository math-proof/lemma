/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Def.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem freeFiniteMeasure_real_le_one (m : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 (Site d)))) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real A ≤ 1 := by
  have := (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)).2
  exact measureReal_le_one


theorem fk_free_limit_exists (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 (fkFreeLimitValue N hp hp1 S)) := by
  set f := fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) with hf
  have hmono := fkFreeLimit_monotone N hp hp1 hS
  have hbdd : BddAbove (Set.range (fun k => f (N+k))) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact freeFiniteMeasure_real_le_one (N+k) hp hp1 _⟩
  
  have hshift : Tendsto (fun k => f (N+k)) atTop (𝓝 (fkFreeLimitValue N hp hp1 S)) :=
    tendsto_atTop_ciSup hmono hbdd
  
  have key : Tendsto (fun k => f (k+N)) atTop (𝓝 (fkFreeLimitValue N hp hp1 S)) := by
    have hcomm : (fun k => f (k+N)) = (fun k => f (N+k)) := by funext k; rw [Nat.add_comm]
    rw [hcomm]; exact hshift
  exact (Filter.tendsto_add_atTop_iff_nat N).mp key


theorem fk_free_le_limit (N m : ℕ) (hNm : N ≤ m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ fkFreeLimitValue N hp hp1 S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNm
  have hbdd : BddAbove (Set.range (fun k => (freeFiniteMeasure d (N+k) hp hp1
        (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d N ⁻¹' S))) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact freeFiniteMeasure_real_le_one (N+k) hp hp1 _⟩
  exact le_ciSup hbdd k


theorem fkFreeLimit_freeInfiniteVolume_eq (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      = fkFreeLimitValue N hp hp1 S := by
  obtain ⟨ψ, hψ, hconv⟩ := freeInfiniteVolume_isLimit d hp hp1 (by norm_num : (0:ℝ) < 2)
  have hclopen := fkFreeLimit_isClopen_preimage N S
  
  have hport := hconv.tendsto_real_of_isClopen (A := boxRestrict d N ⁻¹' S) hclopen
  
  have hsub := (fk_free_limit_exists N hp hp1 hS).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hport hsub


theorem fk_free_infinite_measure (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
  rw [fkFreeLimit_freeInfiniteVolume_eq N hp hp1 hS]
  exact fk_free_limit_exists N hp hp1 hS

end FK
end StatMech
