/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Structure.StatisticalMechanics.Code.Sharpness.FiniteRangePerco
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frp_finset_subset_box (S : Finset (Site d)) :
    ∃ N : ℕ, (S : Set (Site d)) ⊆ box d N := by
  classical
  refine ⟨S.sup (fun x => Finset.univ.sup (fun i => (x i).natAbs)), ?_⟩
  intro x hx
  rw [Finset.mem_coe] at hx
  rw [mem_box]
  intro i
  calc
    (x i).natAbs ≤ Finset.univ.sup (fun j => (x j).natAbs) :=
      Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
    _ ≤ S.sup (fun y => Finset.univ.sup (fun j => (y j).natAbs)) :=
      Finset.le_sup (f := fun y => Finset.univ.sup (fun j => (y j).natAbs)) hx


end Sharpness
end StatMech
