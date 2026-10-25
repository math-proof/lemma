/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure AlignedExactExtentPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k extentX extentY : Nat) where
  raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual extentX extentY
  primalBaseX_eq : raw.data.base 0 =
    family.baseLeft 0 + schedule.horizontal k
  primalEndX_eq : raw.data.base 0 + raw.data.width =
    extentX + family.baseRight 0 - schedule.horizontal k
  primalBaseY_eq : raw.data.base 1 =
    family.baseBottom 1 + schedule.vertical k
  primalEndY_eq : raw.data.base 1 + raw.data.height =
    extentY + family.baseTop 1 - schedule.vertical k
  dualBaseX_eq : raw.data.baseDual 0 =
    familyDual.baseLeft 0 + schedule.horizontal k
  dualEndX_eq : raw.data.baseDual 0 + raw.data.widthDual =
    extentX + familyDual.baseRight 0 - schedule.horizontal k
  dualBaseY_eq : raw.data.baseDual 1 =
    familyDual.baseBottom 1 + schedule.vertical k
  dualEndY_eq : raw.data.baseDual 1 + raw.data.heightDual =
    extentY + familyDual.baseTop 1 - schedule.vertical k
  wideLeft_formula : raw.wideLeftInt =
    pairedWideLeftAtExtentX E Edual family familyDual schedule k extentX
  wideRight_formula : raw.wideRightInt =
    pairedWideRightAtExtentX E Edual family familyDual schedule k extentX


structure PairedAlignedConnectorSlack
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (radius k : Nat) : Prop where
  primalLeft : (E.connectorMarginRequirement radius : Int) <=
    family.baseLeft 0 + schedule.horizontal k
  primalRight : family.baseRight 0 - schedule.horizontal k +
    E.connectorMarginRequirement radius <= 0
  primalBottom : (E.connectorMarginRequirement radius : Int) <=
    family.baseBottom 1 + schedule.vertical k
  primalTop : family.baseTop 1 - schedule.vertical k +
    E.connectorMarginRequirement radius <= 0
  dualLeft : (Edual.connectorMarginRequirement radius : Int) <=
    familyDual.baseLeft 0 + schedule.horizontal k
  dualRight : familyDual.baseRight 0 - schedule.horizontal k +
    Edual.connectorMarginRequirement radius <= 0
  dualBottom : (Edual.connectorMarginRequirement radius : Int) <=
    familyDual.baseBottom 1 + schedule.vertical k
  dualTop : familyDual.baseTop 1 - schedule.vertical k +
    Edual.connectorMarginRequirement radius <= 0


end StatMech.FK.PeriodicPlanar
