module
public import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part2
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


def boxCrossingEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ (x : Site d) (hx : x ∈ box d n), x ∈ vertexBoundary d n ∧
       ∃ (h0 : origin d ∈ box d n),
         ConnectedWithin d ω (box d n) ⟨origin d, h0⟩ ⟨x, hx⟩}

end Percolation
end StatMech
