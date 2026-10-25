/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
open SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc_IsPendantCell (K : Set (Site 2)) (c : Site 2) : Prop :=
  c ∈ K ∧ ∃! u : Site 2, u ∈ K ∧ (hypercubicLattice 2).Adj c u


end Walls
end StatMech
