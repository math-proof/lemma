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
import Instance.StatisticalMechanics.Code.Universality.HexLiteralSubcritical


namespace StatMech.Universality

open HexWalk


theorem hls_exact_length (a : ℂ) (h0 : ℤ) (n : ℕ)
    (d : hls_ExactSAW a h0 n) : d.1.length = n := by
  exact (hlc_mem_sawFinset a h0 n d.1).mp d.2 |>.2


end StatMech.Universality
