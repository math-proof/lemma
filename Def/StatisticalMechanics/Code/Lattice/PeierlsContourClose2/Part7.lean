/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


def ContourGeometryResidue (n ℓ : ℕ) : Prop :=
  ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n →
    contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ →
    ∃ hfin : (↑K : Set (Site 2)).Finite,
      FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin) ∧
      ∃ j : ℕ, j < ℓ ∧ axisVertex 2 j ∈ (boundarySupport hfin : Set (Site 2))


end Lattice
end StatMech
