/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
open Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialBlackDart0 (v : T.Vertex) : FKMedialBlackDart T := by
  let side := if fkMedialVertexParity v then FKMedialSide.south else .west
  refine ⟨(v, side), ?_⟩
  unfold fkMedialCheckerColor side
  by_cases h : fkMedialVertexParity v <;>
    simp [h, fkMedialSideVertical]


def fkMedialBlackDart1 (v : T.Vertex) : FKMedialBlackDart T := by
  let side := if fkMedialVertexParity v then FKMedialSide.north else .east
  refine ⟨(v, side), ?_⟩
  unfold fkMedialCheckerColor side
  by_cases h : fkMedialVertexParity v <;>
    simp [h, fkMedialSideVertical]

end StatMech.FrontierD
