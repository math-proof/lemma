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
import Def.StatisticalMechanics.Code.Lattice.JordanFiniteDetour
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfd_exterior_reachable_deleted (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 (R + 1)) (hy : y ∈ exterior 2 (R + 1)) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable x y := by
  have hmap := (box_exterior_connected (R + 1) (by norm_num) x y hx hy).map
    (jfd_extToDeletedHom H R f0 g0 hHR hf0 hg0)
  simpa [jfd_extToDeletedHom] using hmap


theorem jfd_reconnect_of_both_escape (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    {ef eg : Site 2} (hef : ef ∈ exterior 2 (R + 1)) (heg : eg ∈ exterior 2 (R + 1))
    (hfef : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef)
    (hgeg : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  hfef.trans ((jfd_exterior_reachable_deleted H R f0 g0 hHR hf0 hg0 hef heg).trans hgeg.symm)


end Lattice
end StatMech
