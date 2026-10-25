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
import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices


namespace GraphMatrices

open Matrix SimpleGraph

section LaplacianEigenvalues

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Finset Matrix

structure EdgeOrientation (G : SimpleGraph V) where
  orient : G.edgeSet → V × V
  edge_eq : ∀ e : G.edgeSet, s((orient e).1, (orient e).2) = (e : Sym2 V)

end LaplacianEigenvalues
end GraphMatrices
