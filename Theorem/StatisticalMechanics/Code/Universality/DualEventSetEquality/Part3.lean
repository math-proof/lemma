/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem des_dualV_iff_negH (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    DualVerticalCrossing ω 0 n 0 n ↔ HorizontalCrossing (des_negConfig ω) 0 n (-n) 0 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Inv (x : Site 2), (des_rot90Inv_bottomSide n x).1 x.2⟩,
            ⟨rot90Inv (y : Site 2), (des_rot90Inv_topSide n y).1 y.2⟩, ?_⟩
    exact (hxy : (openSubgraphInduce 2 (dualConfig ω) (rect 0 n 0 n)).Reachable _ _).map
      (des_inducedHom n ω)
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Fun (x : Site 2), ?_⟩, ⟨rot90Fun (y : Site 2), ?_⟩, ?_⟩
    · rw [des_rot90Inv_bottomSide n, show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2
    · rw [des_rot90Inv_topSide n, show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from
        rot90Equiv.left_inv (y : Site 2)]; exact y.2
    · exact (hxy : (openSubgraphInduce 2 (des_negConfig ω) (rect 0 n (-n) 0)).Reachable _ _).map
        (des_inducedHomInv n ω)


theorem des_dualVerticalCrossingEvent_eq (n : ℤ) :
    dualVerticalCrossingEvent 0 n 0 n
      = {ω | HorizontalCrossing (des_negConfig ω) 0 n (-n) 0} := by
  ext ω
  rw [mem_dualVerticalCrossingEvent, Set.mem_setOf_eq, dualVerticalCrossing_iff]
  exact des_dualV_iff_negH ω n


theorem des_hsepSquare_iff_closedH_rotbox (n : ℤ) :
    ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) ↔
      (∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 n 0 n →
        HorizontalCrossing (des_negConfig ω) 0 n (-n) 0) := by
  constructor
  · intro h ω hno
    have : ω ∈ dualVerticalCrossingEvent 0 n 0 n := h (by
      simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact hno)
    rw [mem_dualVerticalCrossingEvent, dualVerticalCrossing_iff] at this
    exact (des_dualV_iff_negH ω n).1 this
  · intro h ω hω
    simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
    rw [mem_dualVerticalCrossingEvent, dualVerticalCrossing_iff]
    exact (des_dualV_iff_negH ω n).2 (h ω hω)


end Universality
end StatMech
