/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaCoupledPairedCut
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) where
  selector : Finset (Copy (lpReplicaCurrentGraph G sites) m)
  half : Finset (LPReplicaCurrentVertex V)
  trueHalf : Finset (LPReplicaCurrentVertex V)
  falseSource0 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag false false ∩ selector) = half
  falseSource1 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag true false ∩ selector) = half
  trueSource0 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag false true ∩ selector) =
      trueHalf.map lpReplicaCurrentReflect.toEmbedding
  trueSource1 : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) m)
    (lpReplicaCurrentCopies G sites m tag true true ∩ selector) = trueHalf
  row0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector)))
    (lpReplicaRowCopies G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector))
      (lpReplicaCoupledReflectToggleTagRaw G sites m selector tag) false)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  row1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector)))
    (lpReplicaRowCopies G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ selector))
        (profileFlux (lpReplicaCurrentGraph G sites) m selector))
      (lpReplicaCoupledReflectToggleTagRaw G sites m selector tag) true)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1


end
end StatMech.Ising
