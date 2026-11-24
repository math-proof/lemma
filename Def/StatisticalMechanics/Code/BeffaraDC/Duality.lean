module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

noncomputable def edgeProductCount (p : ℝ) (m o : ℕ) : ℝ :=
  p ^ o * (1 - p) ^ (m - o)

end BeffaraDC
end StatMech
