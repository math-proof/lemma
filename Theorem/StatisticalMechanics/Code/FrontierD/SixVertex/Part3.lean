module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part4
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

theorem sixVertexRowDistance_comm {N : ℕ} (x y : SixVertexRow N) :
    sixVertexRowDistance x y = sixVertexRowDistance y x := by
  unfold sixVertexRowDistance
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm


end StatMech.FrontierD
