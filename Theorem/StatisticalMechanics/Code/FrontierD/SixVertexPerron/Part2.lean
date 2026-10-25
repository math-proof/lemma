/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem sixVertexSectorPosition_mem {N n : ℕ} (x : SixVertexSector N n)
    (i : Fin n) : sixVertexSectorPosition x i ∈ x.val :=
  Finset.orderEmbOfFin_mem _ _ _

theorem sixVertexSector_upPositions_eq_map_position {N n : ℕ}
    (x : SixVertexSector N n) :
    sixVertexUpPositions (sixVertexSectorRow x) =
      (List.finRange n).map (sixVertexSectorPosition x) := by
  rw [sixVertexSectorRow_upPositions]
  exact (Finset.listMap_orderEmbOfFin_finRange x.val x.prop).symm


end StatMech.FrontierD
