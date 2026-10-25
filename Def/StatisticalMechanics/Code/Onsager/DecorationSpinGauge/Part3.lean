/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part3


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_diagonalGaugeMatrix
    {E : Type*} (gauge : E → ℂ) (M : Matrix E E ℂ) :
    Matrix E E ℂ :=
  fun i j ↦ gauge i * M i j * (gauge j)⁻¹

end StatMech.Onsager
