module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterContour.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


noncomputable def holeFreeAtLen (n ℓ : ℕ) : Finset (Finset (Site 2)) :=
  (holeFreeClusterFamily n).filter
    (fun K => contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ)

end Ising
end StatMech
