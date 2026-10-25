/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

noncomputable def boxPullbackEdgeSubtypes (d n : ℕ)
    (F : Finset (Sym2 (Site d))) :
    Finset (StatMech.FK.boxGraph d (n + 1)).edgeFinset :=
  Finset.univ.filter fun e =>
    StatMech.FK.edgeIncl d (n + 1) e.1 ∈ F

noncomputable def boxPullbackEdgeEquiv
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    ↑(boxPullbackEdgeSubtypes d n F) ≃ ↑F :=
  Equiv.ofBijective
    (fun e => ⟨StatMech.FK.edgeIncl d (n + 1) e.1.1,
      (Finset.mem_filter.mp e.2).2⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact StatMech.FK.edgeIncl_injective d (n + 1)
        (congrArg Subtype.val hab),
    by
      intro e
      have himage := StatMech.IsingFK.hbx_touch_subset_image d n (hF e.2)
      rw [Finset.mem_image] at himage
      obtain ⟨f, hfedge, hfe⟩ := himage
      let fs : (StatMech.FK.boxGraph d (n + 1)).edgeFinset := ⟨f, hfedge⟩
      let z : ↑(boxPullbackEdgeSubtypes d n F) :=
        ⟨fs, by simp [boxPullbackEdgeSubtypes, fs, hfe, e.2]⟩
      exact ⟨z, Subtype.ext hfe⟩⟩

noncomputable def pullbackCurrentPattern
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (a : ↑F → ℕ) :
    ↑(boxPullbackEdgeSubtypes d n F) → ℕ :=
  a ∘ boxPullbackEdgeEquiv d n F hF

noncomputable def pushforwardBoxLocalCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑(boxPullbackEdgeSubtypes d n F) → ℕ) : ↑F → ℕ :=
  a ∘ (boxPullbackEdgeEquiv d n F hF).symm

end StatMech.FrontierB
