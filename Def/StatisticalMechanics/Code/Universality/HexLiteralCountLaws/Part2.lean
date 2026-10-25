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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws


namespace StatMech.Universality

open HexWalk


def hlc_zigzagTurnsAux : Bool → ℕ → List ℤ
  | _, 0 => []
  | false, n + 1 => -1 :: hlc_zigzagTurnsAux true n
  | true, n + 1 => 1 :: hlc_zigzagTurnsAux false n


def hlc_zigzagTurns (n : ℕ) : List ℤ := hlc_zigzagTurnsAux false n

end StatMech.Universality
