module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

def shiftEnv (ω : ℤ → ℝ) : ℤ → ℝ := fun z => ω (z + 1)


end BeffaraDC
end StatMech
