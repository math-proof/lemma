module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part3
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


open Classical in

noncomputable def arc_rayConfig : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k : ℤ, -1 ≤ k ∧ e = s(arc_p k, arc_p (k + 1))) then true else false

end Percolation
end StatMech
