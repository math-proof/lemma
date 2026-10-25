/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


noncomputable def PeriodicPlaneEmbedding.axisSwap
    (E : PeriodicPlaneEmbedding P) : PeriodicPlaneEmbedding P.axisSwap where
  vertex := E.vertex
  period := E.period.comp siteAxisSwapAddEquiv.toAddMonoidHom
  period_injective := E.period_injective.comp siteAxisSwapAddEquiv.injective
  coordinates := E.coordinates.trans axisSwapCoordinates
  coordinates_period z i := by
    change axisSwapCoordinates
      (E.coordinates (E.period (siteAxisSwap z))) i = z i
    rw [axisSwapCoordinates_apply, E.coordinates_period]
    simp [siteAxisSwap]
  vertex_shift z x := E.vertex_shift (siteAxisSwap z) x
  proper := E.proper
  edgeArc := E.edgeArc
  edgeArc_injective := E.edgeArc_injective
  edgeArc_symm := E.edgeArc_symm
  edgeArc_shift z x y hxy := E.edgeArc_shift (siteAxisSwap z) hxy
  edgeArc_intersection := E.edgeArc_intersection
  edgeArc_disjoint := E.edgeArc_disjoint
  edgeArc_locallyFinite := E.edgeArc_locallyFinite

end StatMech.FK.PeriodicPlanar
