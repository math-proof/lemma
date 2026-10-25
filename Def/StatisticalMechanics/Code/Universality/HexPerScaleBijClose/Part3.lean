/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Structure.StatisticalMechanics.Code.Universality.HexPerScaleBijClose


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


noncomputable def hpb_cut (a : ℂ) (h0 : ℤ) (memD memB : List ℤ → Prop)
    (HC : HexHalfClass a h0 hexChiE memD memB)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut_chi a h0 memD {ts // memB ts}
    (fun b => hexSAWwt a h0 hexChiE b.1)
    (fun b => hexSAWwt_nonneg a h0 (le_of_lt hexChiE_pos) b.1)
    (fun d => (HC.lower d, HC.upper d))
    (fun d => HC.hlow d)
    (fun d => HC.hupp d)
    HC.pair_inj
    hDsum hBsum


end StatMech.Universality
