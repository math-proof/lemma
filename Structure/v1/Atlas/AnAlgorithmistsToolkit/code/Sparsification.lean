/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Sparsification
open scoped MatrixOrder ComplexOrder Classical
open Matrix Finset


section WeightedGraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

structure SymmWeights (V : Type*) where
  w : V → V → ℝ
  symm : ∀ i j, w i j = w j i
  diag_zero : ∀ i, w i i = 0

end WeightedGraphOrdering
