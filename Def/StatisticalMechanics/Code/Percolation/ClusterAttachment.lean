/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ClusterAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def cla_AvoidingAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (a : Site d) (w : (openSubgraph d ω).Walk a x),
    (hypercubicLattice d).Adj 0 a ∧
    a ∈ cluster d ω x ∧
    (0 : Site d) ∉ w.support ∧
    (cluster d (removeSite 0 ω) x).Infinite


end Percolation
end StatMech
