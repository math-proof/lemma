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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralSubcritical.Part3


namespace StatMech.Universality

open HexWalk


noncomputable def hls_encodedSix (a : ℂ) (h0 : ℤ) : Finset (Fin 6 → Bool) :=
  (Finset.univ : Finset (hls_ExactSAW a h0 6)).image (hls_encode a h0 6)

end StatMech.Universality
