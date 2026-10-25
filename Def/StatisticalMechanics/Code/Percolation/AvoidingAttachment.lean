/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def ava_AvoidingRoutingResidue (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  x ≠ 0 ∧ (cluster d (removeSite 0 ω) x).Infinite ∧
    ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d (removeSite 0 ω) x


end Percolation
end StatMech
