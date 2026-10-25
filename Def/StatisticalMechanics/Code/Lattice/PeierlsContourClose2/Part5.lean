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
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


noncomputable def dualWalkContour (W : Σ v : Site 2, (hypercubicLattice 2).Walk v v) :
    Finset (Sym2 (Site 2)) :=
  (W.2.edges.map symPrimalSym).toFinset


end Lattice
end StatMech
