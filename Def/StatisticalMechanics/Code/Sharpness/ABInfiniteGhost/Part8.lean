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
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part8
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


noncomputable def abigWindowEdgeEquiv [DecidableEq V] (S : Finset V) :
    Sym2 (Option S) ≃ abigInternalEdges (abigGhostWindow S) :=
  (StatMech.Lattice.sym2Congr (abigGhostWindowEquiv S)).trans
    (abigInternalEdgeEquiv (abigGhostWindow S))

end Sharpness
end StatMech
