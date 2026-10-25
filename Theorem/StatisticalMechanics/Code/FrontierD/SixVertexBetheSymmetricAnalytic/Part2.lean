/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem analyticAt_sixVertexEvenSymmetricBetheResidual_family
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        sixVertexEvenSymmetricBetheResidual N m z.1 z.2) q := by
  let liftPair : (Real × (Fin m → Real)) →L[Real]
      (Real × (Fin (m + m) → Real)) :=
    (ContinuousLinearMap.fst Real Real (Fin m → Real)).prod
      ((sixVertexEvenSymmetricLift m).comp
        (ContinuousLinearMap.snd Real Real (Fin m → Real)))
  let positive : (Fin (m + m) → Real) →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (Fin.natAdd m j)
  have hfull : AnalyticAt Real
      (fun z : Real × (Fin (m + m) → Real) =>
        fun j => sixVertexBetheResidual z.1 N (m + m) z.2 j)
      (q.1, sixVertexEvenSymmetricLift m q.2) :=
    analyticAt_sixVertexBetheResidual_family N (m + m)
      (q.1, sixVertexEvenSymmetricLift m q.2) hc
  have hlift : AnalyticAt Real (liftPair :
      (Real × (Fin m → Real)) → (Real × (Fin (m + m) → Real))) q :=
    liftPair.analyticAt q
  have hcomp : AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        (fun w : Real × (Fin (m + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N (m + m) w.2 j)
            (liftPair z)) q :=
    hfull.comp (f := fun z => liftPair z) (x := q) hlift
  have hpositive := positive.analyticAt
      ((fun z : Real × (Fin (m + m) → Real) =>
        fun j => sixVertexBetheResidual z.1 N (m + m) z.2 j)
          (liftPair q))
  have hout : AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        positive ((fun w : Real × (Fin (m + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N (m + m) w.2 j)
            (liftPair z))) q :=
    hpositive.comp
      (f := fun z : Real × (Fin m → Real) =>
        (fun w : Real × (Fin (m + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N (m + m) w.2 j)
            (liftPair z)) (x := q) hcomp
  have hfun :
      (fun z : Real × (Fin m → Real) =>
        sixVertexEvenSymmetricBetheResidual N m z.1 z.2) =
      (fun z : Real × (Fin m → Real) => fun i =>
        sixVertexBetheResidual z.1 N (m + m)
          (sixVertexEvenSymmetricLift m z.2) (i.addNat m)) := by
    funext z i
    unfold sixVertexEvenSymmetricBetheResidual
    congr 1
    apply Fin.ext
    simp [Fin.natAdd, Fin.addNat]
    omega
  rw [hfun]
  simpa [liftPair, positive, Function.comp_def] using hout

theorem analyticAt_sixVertexEvenSymmetricBetheResidualGraph
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real (sixVertexEvenSymmetricBetheResidualGraph N m) q := by
  exact analyticAt_fst.prod
    (analyticAt_sixVertexEvenSymmetricBetheResidual_family N m q hc)


end
end StatMech.FrontierD
