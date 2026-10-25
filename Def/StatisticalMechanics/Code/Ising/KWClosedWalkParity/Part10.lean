/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part12
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section LatticeBridge

open StatMech.Lattice


noncomputable def latticeSide (S : Set (Site 2)) : Site 2 → Bool :=
  fun x => @decide (x ∈ S) (Classical.propDecidable _)

end LatticeBridge
end Ising
end StatMech
