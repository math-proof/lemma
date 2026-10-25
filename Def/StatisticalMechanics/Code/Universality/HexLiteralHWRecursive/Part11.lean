/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part10


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_pieceSpan (f : ℕ → ℝ) (p : HLHRPiece) : ℝ :=
  |f (p.1 + p.2.length) - f p.1|


noncomputable def hlhr_pieceMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) (lo : ℕ) : ℂ :=
  hexDropMid a h0 ts lo


def hlhr_pieceHead (h0 : ℤ) (ts : List ℤ) (lo : ℕ) : ℤ :=
  h0 + (ts.take lo).sum


end StatMech.Universality
