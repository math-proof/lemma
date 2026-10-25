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


namespace StatMech.Universality

open HexWalk


def hls_ExactSAW (a : ℂ) (h0 : ℤ) (n : ℕ) : Type :=
  {ts : List ℤ // ts ∈ hlc_sawFinset a h0 n}

end StatMech.Universality
