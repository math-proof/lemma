/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Instance.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


theorem abig_map_cfgEquiv (J : Sym2 V -> Real) (beta h : Real)
    (sigma : V ≃ V)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
    Measure.map (cfgEquiv (abfsEdgeEquiv sigma)) (abigMeasure J beta h) =
      abigMeasure J beta h := by
  unfold abigMeasure
  exact inhom_map_cfgEquiv (abigParam J beta h)
    (abigParam_le_one J beta h) (abfsEdgeEquiv sigma)
    (abigParam_invariant J beta h sigma hJ)


end Sharpness
end StatMech
