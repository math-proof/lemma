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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part5


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_intervalsAux (f : ℕ → ℝ) (hi : ℕ) :
    ℕ → Bool → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, up, lo =>
      if lo < hi then
        let k := hlhr_lastExtremum f up lo hi
        (lo, k) :: hlhr_intervalsAux f hi fuel (!up) k
      else []


noncomputable def hlhr_intervalSpan (f : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  |f p.2 - f p.1|

noncomputable def hlhr_intervalSpans (f : ℕ → ℝ) (ps : List (ℕ × ℕ)) :
    List ℝ :=
  ps.map (hlhr_intervalSpan f)


end StatMech.Universality
