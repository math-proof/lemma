/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Ising.OuterContourWindingClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


noncomputable def spinCompatibleFillFinset {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) : Finset (Site 2) :=
  (spinCompatibleFill_finite τ ho).toFinset

end Ising
end StatMech
