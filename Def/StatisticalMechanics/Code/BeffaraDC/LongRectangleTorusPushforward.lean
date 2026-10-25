/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


noncomputable def torusAmbientPMF (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (TorusAmbientConfig L) :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal (torusAmbientProbability L p q omega)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [torusAmbientProbability_sum_one L hp hp1 hq,
          ENNReal.ofReal_one]
      · intro omega _
        exact (div_pos (torusAmbientFKWeight_pos L omega hp hp1 hq)
          (torusAmbientPartition_pos L hp hp1 hq)).le

end StatMech.BeffaraDC
