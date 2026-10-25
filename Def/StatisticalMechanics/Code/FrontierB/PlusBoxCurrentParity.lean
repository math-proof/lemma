/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

noncomputable def boxCurrentInteriorEquiv (d n : ℕ) :
    ↑(boxCurrentInterior d (n + 1)) ≃ StatMech.FK.boxVerts d n :=
  Equiv.ofBijective
    (fun z => ⟨z.1.1, by
      have hnob : ¬ StatMech.FK.boxBoundary d (n + 1) z.1 := by
        exact (Finset.mem_filter.mp z.2).2
      by_contra hx
      exact hnob ((hbx_boxBoundary_succ_iff d n z.1).2 hx)⟩)
    ⟨by
      intro x y hxy
      have hs : x.1.1 = y.1.1 :=
        congrArg (fun z : StatMech.FK.boxVerts d n => z.1) hxy
      exact Subtype.ext (Subtype.ext hs),
    by
      intro x
      let v : StatMech.FK.boxVerts d (n + 1) :=
        ⟨x.1, box_subset_succ d n x.2⟩
      have hvnot : ¬ StatMech.FK.boxBoundary d (n + 1) v := by
        rw [hbx_boxBoundary_succ_iff]
        exact not_not_intro x.2
      let z : ↑(boxCurrentInterior d (n + 1)) :=
        ⟨v, by simp [boxCurrentInterior, hvnot]⟩
      exact ⟨z, Subtype.ext rfl⟩⟩

noncomputable def boxCurrentInteriorConfigEquiv (d n : ℕ) :
    ConfigSpace ↑(boxCurrentInterior d (n + 1)) ≃
      ConfigSpace (StatMech.FK.boxVerts d n) :=
  Equiv.arrowCongr (boxCurrentInteriorEquiv d n) (Equiv.refl Bool)

end StatMech.FrontierB
