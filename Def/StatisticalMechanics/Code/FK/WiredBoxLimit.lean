module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
public import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
public import Theorem.StatisticalMechanics.Code.FK.Limits
public import Theorem.StatisticalMechanics.Code.FK.WiredBoxLimit
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


def innerBdryFinEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (boxVerts d (n+1)))) :=
  innerRestrict d n ⁻¹'
    {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)}


end FK
end StatMech
