/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConcreteSeed.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box


def rcs_pathPairOpen {n : ℤ} (i : RcsPathPair n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_betweenPathOpen i.1 ∩ rlc_betweenPathOpen i.2


end Universality
end StatMech
