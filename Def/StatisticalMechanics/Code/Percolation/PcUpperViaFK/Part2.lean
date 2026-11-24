module
public import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperPeierls
public import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
public import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
public import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
public import Theorem.StatisticalMechanics.Code.FK.Ergodicity
public import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part2
open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperViaFK.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.FK

variable {d : ℕ}


def pcv_edgeEmbed (k : ℕ) : Sym2 (Site 2) → Sym2 (Site (2 + k)) :=
  Sym2.map (pcv_siteEmbed k)

end Percolation
end StatMech
