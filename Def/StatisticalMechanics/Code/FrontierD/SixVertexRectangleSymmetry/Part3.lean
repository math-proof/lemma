/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Mathlib.Data.Fin.Rev
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part2
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleReflectHorizontalEquiv (N M : ℕ) :
    SixVertexRectangleArrows N M ≃ SixVertexRectangleArrows N M :=
  Function.Involutive.toPerm sixVertexRectangleReflectHorizontal
    sixVertexRectangleReflectHorizontal_involutive

def sixVertexRectangleReflectVerticalEquiv (N M : ℕ) :
    SixVertexRectangleArrows N M ≃ SixVertexRectangleArrows N M :=
  Function.Involutive.toPerm sixVertexRectangleReflectVertical
    sixVertexRectangleReflectVertical_involutive

end StatMech.FrontierD
