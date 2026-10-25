/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Instance.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part4
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def triangularEdgePairShapeEquiv :
    Fin 3 ≃ {s : TriangularPairShape // IsTriangularEdgePairShape s} :=
  Equiv.ofBijective
    (fun i => ⟨triangularEdgePairShape i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => triangularEdgePairShape_injective
        (congrArg Subtype.val h),
      fun s => by
        rcases s with ⟨s, i, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩

noncomputable def hexagonalEdgePairShapeEquiv :
    Fin 3 ≃ {s : HexagonalPairShape // IsHexagonalEdgePairShape s} :=
  Equiv.ofBijective
    (fun i => ⟨hexagonalEdgePairShape i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => hexagonalEdgePairShape_injective
        (congrArg Subtype.val h),
      fun s => by
        rcases s with ⟨s, i, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩

def longPairDisplacement (n : Nat) : Site 2 :=
  ![(n : Int) + 2, 0]

end StatMech.FK.PeriodicPlanar
