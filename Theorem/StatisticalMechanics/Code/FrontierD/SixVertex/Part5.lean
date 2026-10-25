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
import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part6
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem sixVertexSectorRow_apply {N n : ℕ} (x : SixVertexSector N n)
    (i : Fin N) : sixVertexSectorRow x i = decide (i ∈ (x : Finset (Fin N))) :=
  rfl

@[simp] theorem sixVertexSectorRow_upCount {N n : ℕ} (x : SixVertexSector N n) :
    sixVertexUpCount (sixVertexSectorRow x) = n := by
  rw [sixVertexUpCount]
  have hx : ({i | sixVertexSectorRow x i} : Finset (Fin N)) = x := by
    ext i
    simp [sixVertexSectorRow]
  rw [hx]
  exact x.prop

@[simp] theorem sixVertexSectorRow_upPositions {N n : ℕ} (x : SixVertexSector N n) :
    sixVertexUpPositions (sixVertexSectorRow x) = (x : Finset (Fin N)).sort (· ≤ ·) := by
  unfold sixVertexUpPositions
  congr 1
  ext i
  simp [sixVertexSectorRow]


end StatMech.FrontierD
