/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.kwffaceclose.Part3
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


noncomputable def lkp_windColour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Site 2 → Bool :=
  fun z => decide (z ∈ jec_leftRegion Vc)


end Walls
end StatMech
