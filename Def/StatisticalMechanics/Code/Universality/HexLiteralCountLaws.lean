/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3


namespace StatMech.Universality

open HexWalk


noncomputable def hlc_sawCount (a : ℂ) (h0 : ℤ) (n : ℕ) : ℕ :=
  hzc_sawCount a h0 (n + 1)


noncomputable def hlc_sawCountR (a : ℂ) (h0 : ℤ) (n : ℕ) : ℝ :=
  (hlc_sawCount a h0 n : ℝ)


end StatMech.Universality
