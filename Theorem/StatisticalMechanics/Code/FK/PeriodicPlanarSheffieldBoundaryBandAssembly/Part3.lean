/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


omit [Countable V] in
theorem PeriodicGraph.componentGridImage_eq_normalShift
    (P : PeriodicGraph V) (S : Finset V)
    (base normal : Site 2) {width height : Nat}
    (v : PreferenceGridVertex width height) :
    ((S.image (P.shift (base + normal))).image
        (P.shift (preferenceGridSite v)) : Set V) =
      P.shift normal ''
        (P.shift (base + preferenceGridSite v) '' (S : Set V)) := by
  ext x
  constructor
  · intro hx
    change x ∈ (S.image (P.shift (base + normal))).image
      (P.shift (preferenceGridSite v)) at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨P.shift (base + preferenceGridSite v) u,
      ⟨u, hu, rfl⟩, ?_⟩
    rw [← P.shift_add, ← P.shift_add]
    congr 2
    abel
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    change P.shift normal (P.shift (base + preferenceGridSite v) u) ∈
      (S.image (P.shift (base + normal))).image
        (P.shift (preferenceGridSite v))
    apply Finset.mem_image.mpr
    refine ⟨P.shift (base + normal) u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [← P.shift_add, ← P.shift_add]
    congr 2
    abel


end StatMech.FK.PeriodicPlanar
