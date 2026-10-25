/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part8
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem selectedLoewnerDuration_spec {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (ht : IsBeforeLoewnerLifetime W z t) :
    IsLoewnerAdmissibleDuration W z (selectedLoewnerDuration ht) ∧
      t < selectedLoewnerDuration ht :=
  Classical.choose_spec (exists_admissibleDuration_gt_of_ofReal_lt_lifetime ht.2)

end StatMech.SLE
