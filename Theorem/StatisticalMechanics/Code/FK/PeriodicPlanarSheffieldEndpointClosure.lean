module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part8
public import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldEndpointClosure
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.ExpandedEndpointSheffieldCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.ExpandedEndpointSheffieldCertificate mu) : False := by
  exact data.level.false_of_alignedEndpoints D mu data.continuation
    data.alignLeft data.alignRight data.alignBottom data.alignTop
    data.B data.Bpos data.primalArcBound data.dualArcBound data.pad_ge
    data.verticalWidth data.verticalHeight data.horizontalWidth
    data.horizontalHeight data.dualVertical data.dualHorizontal


end StatMech.FK.PeriodicPlanar
