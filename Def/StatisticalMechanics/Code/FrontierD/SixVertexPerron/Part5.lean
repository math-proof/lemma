module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part5
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable def sixVertexSectorHeight {N n : ℕ} (x : SixVertexSector N n) : ℕ :=
  ∑ i, (sixVertexSectorPosition x i).val

end StatMech.FrontierD
