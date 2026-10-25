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
import Instance.StatisticalMechanics.Code.FrontierD.SixVertex
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexInterlaced_comm {N : ℕ} (x y : SixVertexRow N) :
    SixVertexInterlaced x y ↔ SixVertexInterlaced y x := by
  simp only [SixVertexInterlaced, or_comm]

theorem sixVertexInterlaced_upCount_eq {N : ℕ} {x y : SixVertexRow N}
    (h : SixVertexInterlaced x y) : sixVertexUpCount x = sixVertexUpCount y := by
  rcases h with h | h
  · exact h.1
  · exact h.1.symm


end StatMech.FrontierD
