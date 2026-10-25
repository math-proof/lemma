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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part8


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_literalIntervals (h0 : ℤ) (ts : List ℤ) :
    List (ℕ × ℕ) :=
  hlhr_intervalsAux (hlhr_height h0 ts) ts.length ts.length true 0


noncomputable def hlhr_literalSpans (h0 : ℤ) (ts : List ℤ) : List ℝ :=
  hlhr_intervalSpans (hlhr_height h0 ts) (hlhr_literalIntervals h0 ts)


end StatMech.Universality
