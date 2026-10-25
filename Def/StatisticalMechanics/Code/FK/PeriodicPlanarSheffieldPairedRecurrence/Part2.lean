/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

noncomputable def pairedWideLeftAtExtentX
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX : Nat) : Int :=
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let left : Site 2 := family.baseLeft + horizontalShift h
  let right : Site 2 := family.baseRight + horizontalShift (-(h : Int))
  let leftDual : Site 2 := familyDual.baseLeft + horizontalShift h
  let rightDual : Site 2 :=
    familyDual.baseRight + horizontalShift (-(h : Int))
  let width := boundaryGridWidth extentX left right
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let baseX := family.baseLeft 0 + h
  let baseXDual := familyDual.baseLeft 0 + h
  let aP := min 0 (min
    (baseX - family.baseBottom 0 - family.radiusBottom v)
    (baseX - family.baseTop 0 - family.radiusTop v))
  let aD := min 0 (min
    (baseXDual - familyDual.baseBottom 0 - familyDual.radiusBottom v)
    (baseXDual - familyDual.baseTop 0 - familyDual.radiusTop v))
  min aP aD


noncomputable def pairedWideRightAtExtentX
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX : Nat) : Int :=
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let left : Site 2 := family.baseLeft + horizontalShift h
  let right : Site 2 := family.baseRight + horizontalShift (-(h : Int))
  let leftDual : Site 2 := familyDual.baseLeft + horizontalShift h
  let rightDual : Site 2 :=
    familyDual.baseRight + horizontalShift (-(h : Int))
  let width := boundaryGridWidth extentX left right
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let baseX := family.baseLeft 0 + h
  let baseXDual := familyDual.baseLeft 0 + h
  let bP : Int := max (extentX : Int) (max
    (baseX + width - family.baseBottom 0 + family.radiusBottom v)
    (baseX + width - family.baseTop 0 + family.radiusTop v))
  let bD : Int := max (extentX : Int) (max
    (baseXDual + widthDual - familyDual.baseBottom 0 +
      familyDual.radiusBottom v)
    (baseXDual + widthDual - familyDual.baseTop 0 +
      familyDual.radiusTop v))
  max bP bD


end StatMech.FK.PeriodicPlanar
