/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


structure HexFiniteStripCoreIncidenceEnumeration
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
  mid_complete : ∀ m ∈ R.mids, ∃ e ∈ D.incidences,
    D.mid e.vtx e.edge = m
  boundary_mid_injective : ∀ e₁ ∈ D.incidences \ P.interior,
    ∀ e₂ ∈ D.incidences \ P.interior,
      D.mid e₁.vtx e₁.edge = D.mid e₂.vtx e₂.edge → e₁ = e₂
  boundary_classified : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge = R.start
      ∨ D.mid e.vtx e.edge ∈ C.sides.bottom
      ∨ D.mid e.vtx e.edge ∈ C.sides.slantPlus
      ∨ D.mid e.vtx e.edge ∈ C.sides.slantMinus
      ∨ D.mid e.vtx e.edge ∈ C.sides.top
  part_unique : ∀ z ∈ R.mids, ∀ k l : Fin 5,
    hexFiniteStripCoreContourPart C k z →
      hexFiniteStripCoreContourPart C l z → k = l
  side_complete : ∀ z ∈ R.mids,
    (z = R.start ∨ z ∈ C.sides.bottom ∨ z ∈ C.sides.slantPlus
      ∨ z ∈ C.sides.slantMinus ∨ z ∈ C.sides.top) →
    ∃ e ∈ D.incidences \ P.interior, D.mid e.vtx e.edge = z


end StatMech.Universality
