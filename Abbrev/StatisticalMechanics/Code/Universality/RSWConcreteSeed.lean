/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConcreteSeed
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box


abbrev RcsRightPath (n : ℤ) := RlcBetweenPath (rcs_rightLower n) (rcs_rightUpper n)

abbrev RcsLeftPath (n : ℤ) := RlcBetweenPath (rcs_leftLower n) (rcs_leftUpper n)

abbrev RcsPathPair (n : ℤ) := RcsRightPath n × RcsLeftPath n

end Universality
end StatMech
