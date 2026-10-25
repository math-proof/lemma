/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part2
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


noncomputable def pfdComponentMap (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent →
      (pfdClosedDual P K).ConnectedComponent :=
  fun C => (pfdClosedDual P K).connectedComponentMk (pfdFace P C.out)


noncomputable def pfdComponentEquiv (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) :
    (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent ≃
      (pfdClosedDual P K).ConnectedComponent := by
  apply Equiv.ofBijective (pfdComponentMap P K)
  constructor
  · intro C D hCD
    have hdual : (pfdClosedDual P K).Reachable (pfdFace P C.out) (pfdFace P D.out) :=
      ConnectedComponent.eq.mp hCD
    have hface := (pfd_regionReachable_iff_dual P K hKP).mpr hdual
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hface
  · intro D
    let C := (whb_faceRegion (jei_pushGraph P K)).connectedComponentMk D.out.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hface : (whb_faceRegion (jei_pushGraph P K)).Reachable C.out D.out.out :=
      ConnectedComponent.exact C.out_eq
    have hdual := pfd_regionReachable_to_dual P K hface
    have hout : pfdFace P D.out.out = D.out := D.out.out_eq
    simpa only [pfdComponentMap, C, hout] using hdual


end BeffaraDC
end StatMech
