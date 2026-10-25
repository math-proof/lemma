/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Def.StatisticalMechanics.Code.Walls.dg2degree.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


theorem dg2_boundary_degree_eq_two_of_bothConnected
    (hres : dg2_NoPinch_of_bothConnected_Statement)
    {K : Set (Site 2)}
    (hK : ((hypercubicLattice 2).induce K).Connected)
    (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 :=
  dg2_boundary_degree_eq_two (hres K hK hKc) hf

end Walls
end StatMech
