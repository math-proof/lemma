/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem exists_positive_compactAnalyticCollar
    (U K : Set Complex) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ epsilon : Real, 0 < epsilon ∧
      Metric.cthickening epsilon K ⊆ U :=
  hK.exists_cthickening_subset_open hU hKU


theorem exists_shift_two_abs_mesh_le
    (mesh : Nat -> Real) (hmesh : Tendsto mesh atTop (nhds 0))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k0 : Nat, forall k, 2 * |mesh (k + k0)| ≤ epsilon := by
  have hscaled : Tendsto (fun k => 2 * |mesh k|) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hmesh.abs
  have heventually : ∀ᶠ k in atTop, 2 * |mesh k| < epsilon :=
    (tendsto_order.1 hscaled).2 epsilon hepsilon
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨k0, fun k => (hk0 (k + k0) ?_).le⟩
  omega


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
