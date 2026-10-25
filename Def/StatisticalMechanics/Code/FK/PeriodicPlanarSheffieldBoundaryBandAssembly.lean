/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.BoundaryBandSeed.toCommonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {width height : Nat} {p : Real}
    (seed : E.BoundaryBandSeed mu S width height p)
    (M : Nat)
    (hleft : seed.radiusLeft ≤ M)
    (hright : seed.radiusRight ≤ M)
    (hbottom : seed.radiusBottom ≤ M)
    (htop : seed.radiusTop ≤ M) :
    E.CommonSquareBoundaryBandData mu S width height M p := by
  let zLeft := seed.baseLeft + horizontalShift (-(M : Int))
  let zRight := seed.baseRight + horizontalShift (M : Int)
  let zBottom := seed.baseBottom + verticalShift (-(M : Int))
  let zTop := seed.baseTop + verticalShift (M : Int)
  refine {
    zLeft := zLeft
    zRight := zRight
    zBottom := zBottom
    zTop := zTop
    left := ?_
    right := ?_
    bottom := ?_
    top := ?_ }
  · intro v
    have hv := E.leftBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusLeft M hleft
      (P.shift (seed.baseLeft + preferenceGridSite v) '' (S : Set V)) p
      (seed.left v).1 (seed.left v).2
    simpa only [zLeft, P.componentGridImage_eq_normalShift] using hv
  · intro v
    have hv := E.rightBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusRight M hright
      (P.shift (seed.baseRight + preferenceGridSite v) '' (S : Set V)) p
      (seed.right v).1 (seed.right v).2
    simpa only [zRight, P.componentGridImage_eq_normalShift] using hv
  · intro v
    have hv := E.bottomBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusBottom M hbottom
      (P.shift (seed.baseBottom + preferenceGridSite v) '' (S : Set V)) p
      (seed.bottom v).1 (seed.bottom v).2
    simpa only [zBottom, P.componentGridImage_eq_normalShift] using hv
  · intro v
    have hv := E.topBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusTop M htop
      (P.shift (seed.baseTop + preferenceGridSite v) '' (S : Set V)) p
      (seed.top v).1 (seed.top v).2
    simpa only [zTop, P.componentGridImage_eq_normalShift] using hv


end StatMech.FK.PeriodicPlanar
