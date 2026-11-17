/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part2
open Finset Matrix

public section

namespace StatMech.FrontierD

@[simp] theorem sixVertexUpPositions_length {N : ℕ} (x : SixVertexRow N) :
    (sixVertexUpPositions x).length = sixVertexUpCount x := by
  simp [sixVertexUpPositions, sixVertexUpCount]


end StatMech.FrontierD
