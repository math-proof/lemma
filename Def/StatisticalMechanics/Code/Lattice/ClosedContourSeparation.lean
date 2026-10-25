/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.ClusterDualContour
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def ccs_OrbitIsLoop (K : Set (Site 2)) : Prop :=
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
    (∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc)) ∧
    (∀ z, z ∉ K → Even (jec_rayCount z Vc))


end Lattice
end StatMech
