module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part4
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable def sixVertexPackedSector (N n : ℕ) (hn : n ≤ N) : SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv
    (OrderEmbedding.ofStrictMono (Fin.castLE hn) (Fin.strictMono_castLE hn))

end StatMech.FrontierD
