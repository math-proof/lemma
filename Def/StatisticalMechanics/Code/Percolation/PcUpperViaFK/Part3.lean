/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperPeierls
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part3
open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.FK

variable {d : ℕ}


def pcv_planeRestrict (k : ℕ)
    (omega : ConfigSpace (Sym2 (Site (2 + k)))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => omega (pcv_edgeEmbed k e)


end Percolation
end StatMech
