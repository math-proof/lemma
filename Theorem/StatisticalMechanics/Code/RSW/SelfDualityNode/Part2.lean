/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.RSW.SelfDualityNode.Part2
open scoped BigOperators ENNReal NNReal
open MeasureTheory


namespace StatMech

namespace RSW

theorem rsd_selfDualPoint_eq (q : ℝ) :
    rsd_selfDualPoint q = BeffaraDC.selfDualPoint q := rfl


theorem rsd_selfDualPoint_mem_Ioo {q : ℝ} (hq : 0 < q) :
    rsd_selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 :=
  BeffaraDC.selfDualPoint_mem_Ioo hq


theorem rsd_selfDual_coupling {q : ℝ} (hq : 0 < q) :
    rsd_dualCoupling (rsd_selfDualPoint q) (rsd_selfDualPoint q) q := by
  
  
  have hmem := BeffaraDC.selfDualPoint_mem_Ioo hq
  have hfix : BeffaraDC.dualParam (BeffaraDC.selfDualPoint q) q
      = BeffaraDC.selfDualPoint q := BeffaraDC.selfDualPoint_is_fixed hq
  have h := rsd_dualParam_coupling hmem.1 hmem.2 hq
  show rsd_dualCoupling (BeffaraDC.selfDualPoint q) (BeffaraDC.selfDualPoint q) q
  rwa [hfix] at h


theorem rsd_selfDual_iff {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    BeffaraDC.dualParam p q = p ↔ p = rsd_selfDualPoint q := by
  constructor
  · intro h; exact BeffaraDC.selfDualPoint_unique hp hp1 hq h
  · intro h; subst h; exact BeffaraDC.selfDualPoint_is_fixed hq


end RSW
end StatMech
