/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem fkWiredLimit_isIncreasing_preimage (N : ℕ)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    IsIncreasing (boxRestrict d N ⁻¹' S) :=
  fun _ _ hab ha => hS (monotone_boxRestrict d N hab) ha


theorem fkWiredLimit_isClopen_preimage (N : ℕ) (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    IsClopen (boxRestrict d N ⁻¹' S) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d N)


theorem fkWiredLimit_measurableSet_preimage (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    MeasurableSet (boxRestrict d N ⁻¹' S) :=
  (fkWiredLimit_isClopen_preimage N S).isOpen.measurableSet


theorem fkWiredLimit_succ_le (N m : ℕ) (hNm : N ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq, wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T hmeas]
  exact wiredFiniteMeasure_succ_le_smallerBox m hp hp1 hTinc hmeas


theorem fkWiredLimit_antitone (N : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Antitone (fun k => (wiredFiniteMeasure d (N+k) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := fkWiredLimit_succ_le N (N+k) (Nat.le_add_right N k) hp hp1 hS
  rw [show N + (k+1) = (N+k)+1 from by ring]
  exact h


end FK
end StatMech
