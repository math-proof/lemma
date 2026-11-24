module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertex.Part5
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

noncomputable def sixVertexSectorTransfer (N n : ℕ) (c : ℝ) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) ℝ :=
  fun x y => sixVertexTransfer N c (sixVertexSectorRow x) (sixVertexSectorRow y)

end StatMech.FrontierD
