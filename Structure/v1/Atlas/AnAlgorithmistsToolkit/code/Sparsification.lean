/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Sparsification
public section

open scoped MatrixOrder ComplexOrder Classical
open Matrix Finset


section WeightedGraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

structure SymmWeights (V : Type*) where
  w : V → V → ℝ
  symm : ∀ i j, w i j = w j i
  diag_zero : ∀ i, w i i = 0

end WeightedGraphOrdering
