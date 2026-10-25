/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Def.StatisticalMechanics.Code.Universality.HexLiteralSubcritical


namespace StatMech.Universality

open HexWalk


noncomputable instance hls_ExactSAW_fintype (a : ℂ) (h0 : ℤ) (n : ℕ) :
    Fintype (hls_ExactSAW a h0 n) := by
  unfold hls_ExactSAW
  infer_instance


end StatMech.Universality
