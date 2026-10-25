/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


theorem ons_weightedEdgeCoefficientIdentity_of_decoratedCycleRemoval
    (L : ℕ) [Fact (2 < L)]
    (hremove : ons_decoratedCycleRemovalIdentity L) :
    ons_weightedEdgeCoefficientIdentity L := by
  intro a b weight q hq hweight hsmall d
  rw [ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib, ← hremove a b weight d]

end StatMech.Onsager
