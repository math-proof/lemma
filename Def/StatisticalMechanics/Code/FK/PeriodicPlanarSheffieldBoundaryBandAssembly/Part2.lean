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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


def PeriodicPlaneEmbedding.NormalBoundaryBandSeed.toCommonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (M : Nat)
    (hleft : seed.radiusLeft ≤ M)
    (hright : seed.radiusRight ≤ M)
    (hbottom : seed.radiusBottom ≤ M)
    (htop : seed.radiusTop ≤ M) :
    E.CommonSquareNormalBoundaryBandData mu S margin M p := by
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
  · intro i
    have hi := E.leftBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusLeft M hleft
      (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)) p
      (seed.left i).1 (seed.left i).2
    simpa only [zLeft, P.normalShift_image_add] using hi
  · intro i
    have hi := E.rightBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusRight M hright
      (P.shift (seed.baseRight + horizontalShift (-(i.val : Int))) ''
        (S : Set V)) p
      (seed.right i).1 (seed.right i).2
    simpa only [zRight, P.normalShift_image_add] using hi
  · intro i
    have hi := E.bottomBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusBottom M hbottom
      (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)) p
      (seed.bottom i).1 (seed.bottom i).2
    simpa only [zBottom, P.normalShift_image_add] using hi
  · intro i
    have hi := E.topBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusTop M htop
      (P.shift (seed.baseTop + verticalShift (-(i.val : Int))) ''
        (S : Set V)) p
      (seed.top i).1 (seed.top i).2
    simpa only [zTop, P.normalShift_image_add] using hi


end StatMech.FK.PeriodicPlanar
