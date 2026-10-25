/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentSingletonMixing
import Def.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK


theorem restrictCurrent_eq_extendLatticeLocalPattern
    (d : Nat) (S : Finset (Sym2 (Site d)))
    (m : InfiniteCurrentConfig (Sym2 (Site d)))
    (hm : ∀ e ∈ S, e ∉ (hypercubicLattice d).edgeSet -> m e = 0) :
    restrictCurrent S m =
      extendLatticeLocalPattern d S
        (restrictCurrent (latticeEdgePart d S) m) := by
  funext e
  by_cases he : e.1 ∈ latticeEdgePart d S
  · simp [extendLatticeLocalPattern, he, restrictCurrent]
  · have hnonlattice : e.1 ∉ (hypercubicLattice d).edgeSet := by
      intro helattice
      exact he (Finset.mem_filter.mpr ⟨e.2, helattice⟩)
    simp [extendLatticeLocalPattern, he, restrictCurrent, hm e.1 e.2 hnonlattice]


theorem currentCylinder_ae_eq_latticeReduction
    (d : Nat)
    (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1)
    (A : Set (↑S -> Nat)) :
    (fun m => m ∈ currentCylinder S A) =ᵐ[(mu : Measure _)]
      (fun m => m ∈ currentCylinder (latticeEdgePart d S)
        (latticeReducedPatternSet d S A)) := by
  have hae := ae_nonlattice_zero_on_finset d mu S hzero
  filter_upwards [hae] with m hm
  apply propext
  change restrictCurrent S m ∈ A ↔
    restrictCurrent (latticeEdgePart d S) m ∈
      latticeReducedPatternSet d S A
  rw [restrictCurrent_eq_extendLatticeLocalPattern d S m hm]
  rfl


end StatMech.FrontierB
