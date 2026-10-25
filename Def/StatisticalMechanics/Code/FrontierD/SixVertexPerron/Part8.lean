/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part8
open Finset Matrix


namespace StatMech.FrontierD

def euclideanAbs {α : Type*} [Fintype α] (v : EuclideanSpace ℝ α) :
    EuclideanSpace ℝ α :=
  WithLp.toLp 2 fun i => |v i|

end StatMech.FrontierD
