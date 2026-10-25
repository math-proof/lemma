/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Def.StatisticalMechanics.Code.Universality.HexW2Weight.Part4


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hexW2_singleRight_split_wt (a : ℂ) (x : ℝ) :
    hexW2_halfWt x (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).1
        = hexSAWwt a 0 x ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)]))
      ∧ hexW2_halfWt x (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).2
        = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]))
            (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) x
            ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) :=
  ⟨hexW2_split_fst_wt a 0 x hexW2_singleRight_memD hexW2_singleRight_elt,
   hexW2_split_snd_wt a 0 x hexW2_singleRight_memD hexW2_singleRight_elt⟩


theorem hexW2_singleRight_split_injective (a : ℂ) :
    Function.Injective (hexW2_split a 0 hexW2_singleRight_memD) :=
  hexW2_split_injective a 0 hexW2_singleRight_memD

end StatMech.Universality
