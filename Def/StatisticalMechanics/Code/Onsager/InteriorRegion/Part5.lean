/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Onsager.InteriorRegion.Part4


namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


def rayWalk (p : Pt) : (N : ℕ) → (hypercubicLattice 2).Walk (toSite p) (toSite (rayX p N))
  | 0 => SimpleGraph.Walk.nil.copy rfl (by simp [rayX])
  | (N + 1) => by
      have adj : (hypercubicLattice 2).Adj (toSite (rayX p N)) (toSite (rayX p (N + 1))) := by
        have h := toSite_adj_shift (rayX p N)
        rwa [shift_ray p N] at h
      exact (rayWalk p N).concat adj


end StatMech.Onsager.InteriorRegion
