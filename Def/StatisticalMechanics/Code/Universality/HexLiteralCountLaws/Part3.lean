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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part2


namespace StatMech.Universality

open HexWalk


noncomputable def hlc_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) : Finset (List ℤ) :=
  (hzc_truncFinset a h0 (n + 2)).filter
    (fun ts => (ofTurns a h0 ts).numVertices = n + 1)

end StatMech.Universality
