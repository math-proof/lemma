/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/GraphMatrices.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices


namespace GraphMatrices

open Matrix SimpleGraph

section LaplacianEigenvalues

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Finset Matrix

variable {G} [Fintype G.edgeSet]

noncomputable def signedIncidenceMatrix : Matrix G.edgeSet V ℝ :=
  fun e v =>
    if v = (σ.orient e).1 then 1
    else if v = (σ.orient e).2 then -1
    else 0

end LaplacianEigenvalues
end GraphMatrices
