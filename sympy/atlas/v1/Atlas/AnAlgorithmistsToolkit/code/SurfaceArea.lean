/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SurfaceArea.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.BrunnMinkowskiInequality
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.BrunnMinkowskiInequality

open Pointwise MeasureTheory Set Filter

namespace SurfaceArea

variable {n : ℕ}

def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

def minkowskiThickening (K : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  K + ε • unitBall n

noncomputable def surfaceArea (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Ioi 0))
    (fun ε => ((volume (minkowskiThickening K ε)).toReal - (volume K).toReal) / ε)
