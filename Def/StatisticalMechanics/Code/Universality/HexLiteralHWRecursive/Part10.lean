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
import Abbrev.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_piecesAux (f : ℕ → ℝ) (hi : ℕ) :
    ℕ → Bool → ℕ → List ℤ → List HLHRPiece
  | 0, _, lo, ts => if ts = [] then [] else [(lo, ts)]
  | fuel + 1, up, lo, ts =>
      if hts : ts = [] then []
      else
        let k := hlhr_cut f up lo hi
        let d := k - lo
        (lo, ts.take d) :: hlhr_piecesAux f hi fuel (!up) k (ts.drop d)


noncomputable def hlhr_pieces (f : ℕ → ℝ) (ts : List ℤ) :
    List HLHRPiece :=
  hlhr_piecesAux f ts.length ts.length true 0 ts


def hlhr_pieceTurns (ps : List HLHRPiece) : List ℤ :=
  (ps.map Prod.snd).flatten


end StatMech.Universality
