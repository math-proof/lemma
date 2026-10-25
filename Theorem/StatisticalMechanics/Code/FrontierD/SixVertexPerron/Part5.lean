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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part4
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem sixVertexSectorPosition_packed (N n : ℕ) (hn : n ≤ N) :
    sixVertexSectorPosition (sixVertexPackedSector N n hn) =
      OrderEmbedding.ofStrictMono (Fin.castLE hn) (Fin.strictMono_castLE hn) := by
  change Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofFinEmbEquiv
        (OrderEmbedding.ofStrictMono (Fin.castLE hn) (Fin.strictMono_castLE hn))) = _
  exact Equiv.symm_apply_apply _ _


end StatMech.FrontierD
