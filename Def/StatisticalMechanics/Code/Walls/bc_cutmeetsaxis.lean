/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConnectProof.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccwitnessnezero
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc_CutMeetsAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ))) ∧
  (cluster d (removeSite 0 ω) x).Infinite


end Walls
end StatMech
