/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaDecoratedOrbitAtomFixedRowGateData
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    {tag : Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites z.1.1.1 A B tag} := by
  let m := z.1.1.1
  let a := z.1.2.1.1
  let Sa := z.1.2.2.1.1
  let Sb := z.1.2.2.2.1
  let P0 := z.2.1.1
  have ha : a <= m := z.1.2.1.2
  have hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a :=
    z.1.2.2.1.2
  have hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B
      (lpReplicaReflectedResidual G sites m a) :=
    z.1.2.2.2.2
  have hP0 : profileFlux (lpReplicaCurrentGraph G sites) m P0 = a :=
    (Finset.mem_filter.mp z.2.1.2).2
  let tag := lpReplicaOrbitCollisionSplitTag G sites m a P0 hP0 Sa Sb
  have hgate := lpReplicaRowGate_orbitCollisionSplitTag
    G sites m a ha P0 hP0 Sa Sb A B hSa hSb
  refine ⟨tag, ?_⟩
  simpa only [m, a, Sa, Sb, P0, tag, hfixed] using hgate


noncomputable def lpReplicaDecoratedOrbitAtomPooledTraceState
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    LPReplicaPooledSelectedSlotState G sites q :=
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites A B q hfixed z
  let e := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
  let K := lpReplicaRowCopies G sites z.1.1.1 d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  lpReplicaPooledSelectedSlotMove G sites q
    (lpReplicaPooledSelectedSlotStateOfCopies
      G sites z.1.1.1 q z.1.1.2 P z.2.2)


end
end StatMech.Ising
