/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Ellipsoid/VolumeContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix Real

namespace EllipsoidMethod

variable {n : ℕ}

noncomputable def Ellipsoid (D : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | dotProduct (x - z) (D⁻¹.mulVec (x - z)) ≤ 1}

noncomputable def updateMatrix (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (D - (2 / ((n : ℝ) + 1)) • (1 / dotProduct a (D.mulVec a)) •
      vecMulVec (D.mulVec a) (D.mulVec a))
