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
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hexW2_highestCut_chi_weightClosed (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable (hexW2_halfWt x)) :
    HexHighestCut x⁻¹ :=
  hexW2_highestCut a h0 hx memD HexW2Half (hexW2_halfWt x)
    (hexW2_halfWt_nonneg x (le_of_lt hx))
    (hexW2_split a h0 memD)
    (fun d => hexW2_split_fst_wt a h0 x memD d)
    (fun d => hexW2_split_snd_wt a h0 x memD d)
    (hexW2_split_injective a h0 memD)
    hDsum hBsum


noncomputable def hexW2_highestCut_chi_weightClosed_chi (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut_chi_weightClosed a h0 hexChiE_pos memD hDsum hBsum


end StatMech.Universality
