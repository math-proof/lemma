/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionRegime
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


def boxOrigin (d n : ℕ) : boxVerts d n := ⟨origin d, origin_mem_box_boxVerts d n⟩


end IsingFK
end StatMech
