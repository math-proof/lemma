/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
open Finset


namespace StatMech.FrontierD

@[ext]
structure SixVertexRectangleArrows (N M : ℕ) where
  horizontal : Fin (N + 1) × Fin M → Bool
  vertical : Fin N × Fin (M + 1) → Bool
deriving DecidableEq, Fintype

end StatMech.FrontierD
