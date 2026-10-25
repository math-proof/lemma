/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate


namespace StatMech

namespace Exact3D

namespace RatInterval

def matVec {m n : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j, A i j * x j


def affineMap {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  matVec A x i + b i


end RatInterval
end Exact3D
end StatMech
