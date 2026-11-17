/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary
public section

open Finset


namespace StatMech.FrontierD

@[ext]
structure SixVertexRectangleBoundary (N M : ℕ) where
  left : Fin M → Bool
  right : Fin M → Bool
  bottom : Fin N → Bool
  top : Fin N → Bool
deriving DecidableEq, Fintype


end StatMech.FrontierD
