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

@[expose] public section

open scoped MatrixOrder ComplexOrder Classical
open Matrix Finset


namespace Sparsification

variable {n : Type*} {𝕜 : Type*} [RCLike 𝕜]

def GraphLoewnerLE (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop :=
  H.lapMatrix ℝ ≤ G.lapMatrix ℝ

def IsSpectralSparsifier (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (ε : ℝ) : Prop :=
  (G.lapMatrix ℝ - (1 - ε) • G'.lapMatrix ℝ).PosSemidef ∧
  ((1 + ε) • G'.lapMatrix ℝ - G.lapMatrix ℝ).PosSemidef

end Sparsification
