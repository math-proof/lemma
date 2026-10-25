/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPerronGaugeThreshold_spec
    {c : Real} (hc : 2 < c) {n : Nat} (hn : 0 < n) :
    ∀ k ≥ sixVertexPerronGaugeThreshold hc n,
      ∃ p, SixVertexHalfFilledPerronGaugeWitness hc k
        ((1 : Real) / (n : Real) ^ 8) p := by
  rw [sixVertexPerronGaugeThreshold, dif_neg hn.ne']
  exact Classical.choose_spec (eventually_atTop.1
    (eventually_exists_sixVertexHalfFilledPerronGaugeWitness
      (epsilon := (1 : Real) / (n : Real) ^ 8) hc
      (by
        apply one_div_pos.mpr
        positivity)))

@[simp] theorem sixVertexPerronGaugeThreshold_zero
    {c : Real} (hc : 2 < c) :
    sixVertexPerronGaugeThreshold hc 0 = 0 := by
  simp [sixVertexPerronGaugeThreshold]


end
end StatMech.FrontierD
