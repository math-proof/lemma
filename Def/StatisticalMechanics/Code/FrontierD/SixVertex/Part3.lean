/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertex
open Finset Matrix


namespace StatMech.FrontierD

def sixVertexAlternating {N : ℕ} (x y : SixVertexRow N) : List (Fin N) :=
  (sixVertexUpPositions x).zip (sixVertexUpPositions y) |>.flatMap
    fun p => [p.1, p.2]


def SixVertexForwardInterlaced {N : ℕ} (x y : SixVertexRow N) : Prop :=
  sixVertexUpCount x = sixVertexUpCount y ∧
    (sixVertexAlternating x y).Pairwise (· ≤ ·)


def SixVertexInterlaced {N : ℕ} (x y : SixVertexRow N) : Prop :=
  SixVertexForwardInterlaced x y ∨ SixVertexForwardInterlaced y x

end StatMech.FrontierD
