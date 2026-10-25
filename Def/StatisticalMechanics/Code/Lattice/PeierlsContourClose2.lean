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
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


noncomputable def symPrimal (f g : Site 2) : Sym2 (Site 2) := by
  classical
  exact if f 0 = g 0 then
    s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)])
  else
    s(![max (f 0) (g 0), min (f 1) (g 1)], ![max (f 0) (g 0), min (f 1) (g 1) + 1])


end Lattice
end StatMech
