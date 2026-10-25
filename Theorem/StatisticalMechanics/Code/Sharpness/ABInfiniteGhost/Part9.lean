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
import Def.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part8
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


@[simp] theorem abigWindowEdgeEquiv_mk [DecidableEq V] (S : Finset V)
    (a b : Option S) :
    (abigWindowEdgeEquiv S s(a, b) : Sym2 (Option V)) =
      s((abigGhostWindowEquiv S a : Option V),
        (abigGhostWindowEquiv S b : Option V)) := by
  simp [abigWindowEdgeEquiv, StatMech.Lattice.sym2Congr_mk]


end Sharpness
end StatMech
