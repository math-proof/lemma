/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFiniteDetour
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jfd_extToDeletedHom (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R) :
    (hypercubicLattice 2).induce (exterior 2 (R + 1)) →g
      (whb_faceRegion H).deleteEdges {s(f0, g0)} where
  toFun v := (v : Site 2)
  map_rel' := by
    intro a b hab
    exact jfd_deleted_adj_of_exterior H R f0 g0 hHR hf0 hg0 a.2 b.2 hab


end Lattice
end StatMech
