/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part3
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusCellCrossingCode (L : ℕ) : TorusEdgeCode L ≃ TorusEdgeCode L where
  toFun
    | ((x, y), .horizontal) => ((x, y - 1), .vertical)
    | ((x, y), .vertical) => ((x - 1, y), .horizontal)
  invFun
    | ((x, y), .horizontal) => ((x + 1, y), .vertical)
    | ((x, y), .vertical) => ((x, y + 1), .horizontal)
  left_inv c := by rcases c with ⟨⟨x, y⟩, o⟩; cases o <;> simp
  right_inv c := by rcases c with ⟨⟨x, y⟩, o⟩; cases o <;> simp


noncomputable def torusCellCrossing (L : ℕ) [Fact (2 < L)] :
    TorusAmbientEdge L ≃ TorusAmbientEdge L :=
  (torusEdgeCodeEquiv L).symm.trans
    ((torusCellCrossingCode L).trans (torusEdgeCodeEquiv L))

end StatMech.BeffaraDC
