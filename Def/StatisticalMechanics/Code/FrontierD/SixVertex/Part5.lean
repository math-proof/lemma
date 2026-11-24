module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertex.Part3
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

noncomputable def sixVertexTransfer (N : ℕ) (c : ℝ) :
    Matrix (SixVertexRow N) (SixVertexRow N) ℝ := by
  classical
  exact fun x y => if x = y then 2
    else if SixVertexInterlaced x y then c ^ sixVertexRowDistance x y else 0

end StatMech.FrontierD
