/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part3


namespace StatMech

namespace Exact3D

namespace StableBlockWithRemainder

noncomputable def coordinateConstant {n : ℕ} (S : StableBlockWithRemainder n) : ℝ :=
  ((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ)


noncomputable def l1StepConstant {n : ℕ} (S : StableBlockWithRemainder n) : ℝ :=
  (n : ℝ) * S.coordinateConstant


noncomputable def iterate {n : ℕ} (S : StableBlockWithRemainder n) :
    ℕ → (Fin n → ℝ) → Fin n → ℝ
  | 0, x => x
  | k + 1, x => S.step (S.iterate k x)


end StableBlockWithRemainder
end Exact3D
end StatMech
