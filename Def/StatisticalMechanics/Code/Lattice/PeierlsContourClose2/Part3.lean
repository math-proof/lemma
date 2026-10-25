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
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


noncomputable def flankFaces (p q : Site 2) : Sym2 (Site 2) := by
  classical
  exact if p 0 = q 0 then
    s(![p 0 - 1, min (p 1) (q 1)], ![p 0, min (p 1) (q 1)])
  else
    s(![min (p 0) (q 0), min (p 1) (q 1) - 1], ![min (p 0) (q 0), min (p 1) (q 1)])


end Lattice
end StatMech
