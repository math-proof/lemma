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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexPackedSector (N n : ℕ) (hn : n ≤ N) : SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv
    (OrderEmbedding.ofStrictMono (Fin.castLE hn) (Fin.strictMono_castLE hn))

end StatMech.FrontierD
