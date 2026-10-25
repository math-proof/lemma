/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def bma_ClusterAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (a : Site d) (W : Finset (Sym2 (Site d))),
    (hypercubicLattice d).Adj 0 a ∧
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    (∀ e ∈ W, ∀ p, p ∈ e → p ∈ cluster d ω x) ∧
    a ∈ cluster d ω x ∧
    Connected d (removeSite 0 (forceOpenFinset W ω)) a x ∧
    (cluster d (removeSite 0 ω) x).Infinite


end Percolation
end StatMech
