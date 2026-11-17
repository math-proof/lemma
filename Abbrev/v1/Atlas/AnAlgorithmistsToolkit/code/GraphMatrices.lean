/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/GraphMatrices.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Real.Basic

@[expose] public section


namespace GraphMatrices

open Matrix SimpleGraph

section AdjMatrix

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable abbrev adjMatrix : Matrix V V ℝ :=
  G.adjMatrix ℝ

end AdjMatrix
end GraphMatrices
