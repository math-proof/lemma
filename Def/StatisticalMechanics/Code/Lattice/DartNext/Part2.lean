/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext
open SimpleGraph


namespace StatMech

namespace Lattice

def mkDart (p g : Site 2) (hg : unitWt g = 1) : Dart where
  tail := p
  head := p + g
  adj := by
    rw [adj_iff_unitWt_sub, show p - (p + g) = -g by abel, unitWt_neg]
    exact hg

end Lattice
end StatMech
