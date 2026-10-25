/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part17
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triHexPairShapeEquiv_edge (i : Fin 3) :
    triHexPairShapeEquiv (triangularEdgePairShape i) =
      hexagonalEdgePairShape i := by
  unfold triHexPairShapeEquiv
  simp only [Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos ⟨i, rfl⟩]
  change (Equiv.sumCompl IsHexagonalEdgePairShape)
    (Sum.inl (hexagonalEdgePairShapeEquiv
      (triangularEdgePairShapeEquiv.symm
        ⟨triangularEdgePairShape i, ⟨i, rfl⟩⟩))) = _
  rw [show (⟨triangularEdgePairShape i, ⟨i, rfl⟩⟩ :
      {s : TriangularPairShape // IsTriangularEdgePairShape s}) =
        triangularEdgePairShapeEquiv i by rfl]
  simp [hexagonalEdgePairShapeEquiv]


end StatMech.FK.PeriodicPlanar
