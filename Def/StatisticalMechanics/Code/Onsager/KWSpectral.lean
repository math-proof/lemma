/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Theorem.StatisticalMechanics.Code.Onsager.DetWalkExp
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral


namespace StatMech.Onsager

noncomputable def ons_KWconvergenceRadius (L : ℕ) [NeZero L] : ℝ :=
  (Fintype.card (ons_Dart L) : ℝ)⁻¹

end StatMech.Onsager
