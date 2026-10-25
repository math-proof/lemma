/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaTagEquiv
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part2
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaRowGate_orbitCollisionSplitTag
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (ha : a <= m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a)))
    (A B : Finset (LPReplicaCurrentVertex V))
    (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a)
    (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B
      (lpReplicaReflectedResidual G sites m a)) :
    LPReplicaRowGate G sites m A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaOrbitCollisionSplitTag G sites m a P hP Sa Sb) := by
  let b := lpReplicaReflectedResidual G sites m a
  let E := lpReplicaOrbitCollisionSplitEquiv G sites m a P hP
  have hcanonical := lpReplicaCollisionRowGate_of_mem_disconnFamilies
    G sites a b Sa Sb A B hSa hSb
  have htransport := lpReplicaRowGate_transportTag G sites E.symm (by
    intro c
    have h := lpReplicaOrbitCollisionSplitEquiv_ends
      G sites m a P hP (E.symm c)
    simpa [E] using h.symm) A (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCollisionRowTag G sites a b Sa Sb) hcanonical
  have hprofile : lpReplicaCollisionProfile G sites a b = m :=
    lpReplicaCollision_projection G sites m a ha
  simpa only [b, E, lpReplicaOrbitCollisionSplitTag, hprofile] using htransport

end
end StatMech.Ising
