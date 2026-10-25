/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem analyticAt_sixVertexOddSymmetricBetheResidual_family
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        sixVertexOddSymmetricBetheResidual N m z.1 z.2) q := by
  let liftPair : (Real × (Fin m → Real)) →L[Real]
      (Real × (Fin ((m + 1) + m) → Real)) :=
    (ContinuousLinearMap.fst Real Real (Fin m → Real)).prod
      ((sixVertexOddSymmetricLift m).comp
        (ContinuousLinearMap.snd Real Real (Fin m → Real)))
  let positive : (Fin ((m + 1) + m) → Real) →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.proj (sixVertexOddPositiveIndex m j)
  have hfull : AnalyticAt Real
      (fun z : Real × (Fin ((m + 1) + m) → Real) =>
        fun j => sixVertexBetheResidual z.1 N ((m + 1) + m) z.2 j)
      (q.1, sixVertexOddSymmetricLift m q.2) :=
    analyticAt_sixVertexBetheResidual_family N ((m + 1) + m)
      (q.1, sixVertexOddSymmetricLift m q.2) hc
  have hlift : AnalyticAt Real (liftPair :
      (Real × (Fin m → Real)) →
        (Real × (Fin ((m + 1) + m) → Real))) q := liftPair.analyticAt q
  have hcomp : AnalyticAt Real
      (fun z : Real × (Fin m → Real) =>
        (fun w : Real × (Fin ((m + 1) + m) → Real) =>
          fun j => sixVertexBetheResidual w.1 N ((m + 1) + m) w.2 j)
            (liftPair z)) q :=
    hfull.comp (f := fun z => liftPair z) (x := q) hlift
  have hpositive := positive.analyticAt
    ((fun w : Real × (Fin ((m + 1) + m) → Real) =>
      fun j => sixVertexBetheResidual w.1 N ((m + 1) + m) w.2 j)
        (liftPair q))
  have hout := hpositive.comp hcomp
  simpa [liftPair, positive, sixVertexOddSymmetricBetheResidual,
    sixVertexOddPositiveIndex, Function.comp_def] using hout

theorem analyticAt_sixVertexOddSymmetricBetheResidualGraph
    (N m : Nat) (q : Real × (Fin m → Real)) (hc : 2 < q.1) :
    AnalyticAt Real (sixVertexOddSymmetricBetheResidualGraph N m) q :=
  analyticAt_fst.prod
    (analyticAt_sixVertexOddSymmetricBetheResidual_family N m q hc)

end
end StatMech.FrontierD
