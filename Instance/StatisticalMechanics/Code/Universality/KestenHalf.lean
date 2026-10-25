/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.Universality.KestenHalf
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


instance instIsProbabilityMeasure_halfMeasure : IsProbabilityMeasure halfMeasure := by
  unfold halfMeasure; infer_instance


end Universality
end StatMech
