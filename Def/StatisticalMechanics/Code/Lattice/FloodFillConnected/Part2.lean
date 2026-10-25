/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def ffc_lift_walk {B : Set (Site 2)} :
    ∀ {x y : Site 2} (p : (hypercubicLattice 2).Walk x y),
      (∀ z ∈ p.support, z ∉ B) → (ffc_offSupportLattice B).Walk x y
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons hab p, hp =>
      SimpleGraph.Walk.cons
        ⟨hab, hp _ (by simp), hp _ (by
          rw [SimpleGraph.Walk.support_cons]; right; exact p.start_mem_support)⟩
        (ffc_lift_walk p (fun z hz => hp z (by
          rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)))


end Lattice
end StatMech
