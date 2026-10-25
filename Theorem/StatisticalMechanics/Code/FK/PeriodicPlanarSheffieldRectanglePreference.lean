/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S side : Set V) :
    MeasurableSet (E.rectSideConnectionEvent a b c d S side) :=
  P.infiniteSetConnectionWithin_measurableSet
    (E.rectVertices a b c d) S side

theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S side : Set V) :
    IsIncreasing (E.rectSideConnectionEvent a b c d S side) :=
  P.infiniteSetConnectionWithin_isIncreasing
    (E.rectVertices a b c d) S side


theorem PeriodicPlaneEmbedding.setHitsInfinite_subset_rectSideConnection_union
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d) :
    P.setHitsInfinite S ⊆
      E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d) ∪
        (E.rectSideConnectionEvent a b c d S
            (E.rectTopBoundaryVertices a b c d) ∪
          (E.rectSideConnectionEvent a b c d S
              (E.rectLeftBoundaryVertices a b c d) ∪
            E.rectSideConnectionEvent a b c d S
              (E.rectRightBoundaryVertices a b c d))) := by
  intro omega homega
  obtain ⟨x, hxS, hxinf⟩ := homega
  obtain ⟨y, hycluster, hyout⟩ :=
    hxinf.exists_notMem_finite (E.rectVertices_finite a b c d)
  obtain ⟨p⟩ := hycluster
  obtain ⟨v, hvRect, z, hvz, hzout, q, hqRect, _hqsub⟩ :=
    P.exists_boundary_walk_of_walk_to_compl omega
      (E.rectVertices a b c d) p (hS hxS) hyout
  have hxv : omega ∈ P.connectedWithinSet (E.rectVertices a b c d) x v :=
    P.mem_connectedWithinSet_of_walk q hqRect
  by_cases hzLeft : E.vertexCoord z 0 < a
  · exact Or.inr (Or.inr (Or.inl
      ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzLeft⟩, hxv⟩))
  by_cases hzRight : b < E.vertexCoord z 0
  · exact Or.inr (Or.inr (Or.inr
      ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzRight⟩, hxv⟩))
  by_cases hzBottom : E.vertexCoord z 1 < c
  · exact Or.inl ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzBottom⟩, hxv⟩
  have hzTop : d < E.vertexCoord z 1 := by
    apply lt_of_not_ge
    intro hzd
    apply hzout
    exact ⟨le_of_not_gt hzLeft, le_of_not_gt hzRight,
      le_of_not_gt hzBottom, hzd⟩
  exact Or.inr (Or.inl
    ⟨x, hxS, hxinf, v, ⟨hvRect, z, hvz, hzTop⟩, hxv⟩)


end StatMech.FK.PeriodicPlanar
