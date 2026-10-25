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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part2
open Finset Matrix


namespace StatMech.FrontierD

def SixVertexPositionsForwardInterlaced {N n : ℕ}
  (x y : SixVertexSector N n) : Prop :=
  (∀ i, sixVertexSectorPosition x i ≤ sixVertexSectorPosition y i) ∧
    (∀ (k : ℕ) (hk : k + 1 < n),
      sixVertexSectorPosition y ⟨k, by omega⟩ ≤
        sixVertexSectorPosition x ⟨k + 1, hk⟩)

end StatMech.FrontierD
