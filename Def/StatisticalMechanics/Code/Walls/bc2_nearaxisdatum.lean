/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}


def bc2_NearAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  hrHD_rayPt j 1 ∈ cluster d ω x ∧
    Connected d (removeSite 0 ω) (hrHD_rayPt j 1) x ∧
    (cluster d (removeSite 0 ω) x).Infinite


end Walls
end StatMech
