/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

def ndt_sublevel (φ ψ : ℤ → ℤ) (c : ℤ) : Set (Site 2) := {x | φ (x 0) + ψ (x 1) ≤ c}


end Lattice
end StatMech
