/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.SLE.Defs.Part2
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

lemma LoewnerChain.continuous_driving (c : LoewnerChain) : Continuous c.driving :=
  c.driving_continuous


lemma LoewnerChain.maps_zero (c : LoewnerChain) (z : ℂ) : c.maps 0 z = z :=
  c.loewner.1 z


end StatMech.SLE
