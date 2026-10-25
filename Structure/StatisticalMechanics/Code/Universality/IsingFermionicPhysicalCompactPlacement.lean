/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part3


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalStripMapTraceRangeData
    (N : Nat -> Nat) (Phi : Complex -> Complex)
    (mesh : Nat -> Real) : Prop where
  range : Set.MapsTo Phi
    (physicalFullSquareSampleCarrier N mesh)
    isingFermionicClosedUnitStrip
  lowerTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
    (physicalFullSquareLowerTraceCarrier N mesh)
  upperTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
    (physicalFullSquareUpperTraceCarrier N mesh)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
