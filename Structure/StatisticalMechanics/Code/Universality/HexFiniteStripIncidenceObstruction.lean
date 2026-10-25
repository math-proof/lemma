/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part3


namespace StatMech.Universality

open Complex HexWalk Set


structure HexFiniteStripIncidenceEnumeration
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (B : HexFiniteStripBoundaryData R h0 D P) where
  
  mid_complete : ∀ m ∈ R.mids, ∃ e ∈ D.incidences,
    D.mid e.vtx e.edge = m
  
  boundary_mid_injective : ∀ e₁ ∈ D.incidences \ P.interior,
    ∀ e₂ ∈ D.incidences \ P.interior,
      D.mid e₁.vtx e₁.edge = D.mid e₂.vtx e₂.edge → e₁ = e₂
  

  boundary_classified : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge = R.start
      ∨ D.mid e.vtx e.edge ∈ B.sides.bottom
      ∨ D.mid e.vtx e.edge ∈ B.sides.slantPlus
      ∨ D.mid e.vtx e.edge ∈ B.sides.slantMinus
      ∨ D.mid e.vtx e.edge ∈ B.sides.top
  
  part_unique : ∀ z ∈ R.mids, ∀ k l : Fin 5,
    hexFiniteStripContourPart B k z →
      hexFiniteStripContourPart B l z → k = l
  

  side_complete : ∀ z ∈ R.mids,
    (z = R.start ∨ z ∈ B.sides.bottom ∨ z ∈ B.sides.slantPlus
      ∨ z ∈ B.sides.slantMinus ∨ z ∈ B.sides.top) →
    ∃ e ∈ D.incidences \ P.interior, D.mid e.vtx e.edge = z


end StatMech.Universality
