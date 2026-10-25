/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology BigOperators


noncomputable def hbs_highestCut (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (hexW2_halfWt hexChiE)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut_chi_weightClosed a h0 hexChiE_pos memD hDsum hBsum


end StatMech.Universality
