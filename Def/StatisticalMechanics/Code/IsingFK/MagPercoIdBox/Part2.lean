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
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part2
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def boxBoundaryConnProfile (d : ℕ) {p : ℝ} (_hp : 0 < p) (_hp1 : p < 1)
    (_hq : (0 : ℝ) < 2) (n : ℕ) : ℝ :=
  wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p (boxOrigin d n)


end IsingFK
end StatMech
