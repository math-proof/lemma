module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part4
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable def sixVertexFiniteTorusRowPartitionSum (T : EvenTorus) (c : ℝ) : ℝ :=
  sixVertexPeriodicRowPartitionSum T.width T.height T.height_pos c


end StatMech.FrontierD
