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
import Def.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part2


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


theorem hpb_lamS_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (memA : List ℤ → Prop) :
    0 ≤ hpb_lamS a h0 x memA :=
  tsum_nonneg (fun d => hexSAWwt_nonneg a h0 hx d.1)


theorem hpb_upsS_nonneg (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (memB : List ℤ → Prop) :
    0 ≤ hpb_upsS a h0 x memB :=
  tsum_nonneg (fun b => hexSAWwt_nonneg a h0 hx b.1)


end StatMech.Universality
