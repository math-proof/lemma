/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4
import Def.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hhe_singleRight_upper_fires (a : ℂ) (x : ℝ) :
    hexSAWwt a 0 x
        ((hhe_halfClass_of_halves a 0 x hexW2_singleRight_memD hhe_singleRight_memB
            hhe_singleRight_halvesInColumn).upper hexW2_singleRight_elt).1
      = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]))
          (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) x
          ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) :=
  (hhe_halfClass_of_halves a 0 x hexW2_singleRight_memD hhe_singleRight_memB
    hhe_singleRight_halvesInColumn).hupp hexW2_singleRight_elt

end StatMech.Universality
