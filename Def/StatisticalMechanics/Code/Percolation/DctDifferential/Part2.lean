module
public import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential
open MeasureTheory Function Set
open scoped NNReal
open StatMech


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def boxEdgeFinset (d n : ℕ) : Finset (Sym2 (Site d)) :=
  ((boxFinset d n) ×ˢ (boxFinset d n)).image (fun p => s(p.1, p.2))

end Percolation
end StatMech
