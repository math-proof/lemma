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
