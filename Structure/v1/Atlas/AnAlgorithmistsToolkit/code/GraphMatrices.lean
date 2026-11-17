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
public import Abbrev.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices


public section

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
