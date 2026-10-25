/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNearBoundary
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def siteNegAddEquiv : Site 2 ≃+ Site 2 where
  toFun := siteNeg
  invFun := siteNeg
  left_inv := siteNeg_neg
  right_inv := siteNeg_neg
  map_add' := siteNeg_add

def PeriodicGraph.axisNeg (P : PeriodicGraph V) : PeriodicGraph V where
  graph := P.graph
  shift z := P.shift (siteNeg z)
  shift_zero := by simpa using P.shift_zero
  shift_add z w v := by simpa using P.shift_add (siteNeg z) (siteNeg w) v
  shift_adj z x y := P.shift_adj (siteNeg z) x y
  fundamentalDomain := P.fundamentalDomain
  fundamentalDomain_nonempty := P.fundamentalDomain_nonempty
  covers v := by
    obtain ⟨z, u, hu, hzu⟩ := P.covers v
    exact ⟨siteNeg z, u, hu, by simpa [siteNeg_neg] using hzu⟩
  locallyFinite := P.locallyFinite

noncomputable def PeriodicPlaneEmbedding.axisNeg
    (E : PeriodicPlaneEmbedding P) : PeriodicPlaneEmbedding P.axisNeg where
  vertex := E.vertex
  period := E.period.comp siteNegAddEquiv.toAddMonoidHom
  period_injective := E.period_injective.comp siteNegAddEquiv.injective
  coordinates := E.coordinates.trans (ContinuousLinearEquiv.neg Real)
  coordinates_period z i := by
    change -(E.coordinates (E.period (siteNeg z))) i = z i
    rw [E.coordinates_period]
    simp [siteNeg]
  vertex_shift z x := E.vertex_shift (siteNeg z) x
  proper := E.proper
  edgeArc := E.edgeArc
  edgeArc_injective := E.edgeArc_injective
  edgeArc_symm := E.edgeArc_symm
  edgeArc_shift z x y hxy := E.edgeArc_shift (siteNeg z) hxy
  edgeArc_intersection := E.edgeArc_intersection
  edgeArc_disjoint := E.edgeArc_disjoint
  edgeArc_locallyFinite := E.edgeArc_locallyFinite

end StatMech.FK.PeriodicPlanar
