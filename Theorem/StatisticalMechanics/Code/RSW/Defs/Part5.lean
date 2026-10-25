/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.RSW.Defs.Part5
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp]
theorem mem_annulus {z x : Site 2} {n : ℕ} :
    x ∈ annulus z n ↔ ∃ y, (y ∈ box 2 (2 * n) ∧ y ∉ box 2 n) ∧ z + y = x := by
  simp only [annulus, Set.mem_image, Set.mem_diff, mem_box]


theorem annulus_finite (z : Site 2) (n : ℕ) : (annulus z n).Finite :=
  ((box_finite 2 (2 * n)).diff).image _


theorem annulus_subset_outer (z : Site 2) (n : ℕ) :
    annulus z n ⊆ (fun x => z + x) '' box 2 (2 * n) :=
  Set.image_mono Set.diff_subset


end Box
end RSW
end StatMech
