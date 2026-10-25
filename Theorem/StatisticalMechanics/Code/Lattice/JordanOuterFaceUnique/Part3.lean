/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem geometricRegionCount_add_one_eq_card
    (P : PlanarZ2Subgraph)
    [Finite (regionGraph (imageGraph P)).ConnectedComponent] :
    geometricRegionCount P + 1 =
      Nat.card (regionGraph (imageGraph P)).ConnectedComponent := by
  unfold geometricRegionCount
  rw [Nat.card_congr (boundedRegionEquivNeOuter P), card_subtype_ne_add_one]


theorem faceCount_eq_boundedRegions_with_unique_outer (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    faceCount P.G = geometricRegionCount P + 1 ∧
      (outerRegion P).supp.Infinite ∧
      (∀ C : (regionGraph (imageGraph P)).ConnectedComponent,
        C.supp.Infinite → C = outerRegion P) ∧
      (∀ C : (regionGraph (imageGraph P)).ConnectedComponent,
        C.supp.Finite ↔ C ≠ outerRegion P) :=
  ⟨faceCount_eq_geometric_regions P hJ,
   outerRegion_infinite P,
   fun _ hC => outerRegion_eq_of_infinite P hC,
   boundedRegion_iff_ne_outer P⟩

end Lattice
end StatMech
