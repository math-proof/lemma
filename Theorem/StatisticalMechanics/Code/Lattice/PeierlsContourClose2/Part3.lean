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
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem flankFaces_comm (p q : Site 2) : flankFaces p q = flankFaces q p := by
  classical
  unfold flankFaces
  by_cases h0 : p 0 = q 0
  · rw [if_pos h0, if_pos h0.symm, h0, min_comm]
  · rw [if_neg h0, if_neg (fun hc => h0 hc.symm), min_comm (p 0), min_comm (p 1)]


end Lattice
end StatMech
