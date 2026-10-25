/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part7
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem isBeforeLoewnerLifetime_iff_exists_admissible
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    IsBeforeLoewnerLifetime W z t ↔
      ∃ T, IsLoewnerAdmissibleDuration W z T ∧ t < T := by
  constructor
  · intro h
    exact exists_admissibleDuration_gt_of_ofReal_lt_lifetime h.2
  · rintro ⟨T, hT, htT⟩
    refine ⟨ht, ?_⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff hT.1).2 htT).trans_le
      (ofReal_le_loewnerLifetime hT)

end StatMech.SLE
