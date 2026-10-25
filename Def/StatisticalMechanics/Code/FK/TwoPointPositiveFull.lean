/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneErgodic
open MeasureTheory Filter Topology


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def infiniteTwoPointReal
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) (x y : Site d) : ℝ :=
  μ.real {ω | StatMech.Lattice.Connected d ω x y}


def clusterInfiniteEvent (d : ℕ) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (cluster d ω x).Infinite}

end FK
end StatMech
