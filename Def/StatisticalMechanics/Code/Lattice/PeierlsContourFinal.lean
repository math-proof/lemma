/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


noncomputable def componentSupport (K : Set (Site 2)) (T : Finset (Site 2)) (f : Site 2) :
    Finset (Site 2) :=
  T.filter (fun g => (faceBoundaryGraph K).Reachable f g)

end Lattice
end StatMech
