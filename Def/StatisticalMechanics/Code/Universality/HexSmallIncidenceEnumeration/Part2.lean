/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Structure.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


def HexFiniteStripIncidenceEnumeration.toCore
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) :
    HexFiniteStripCoreIncidenceEnumeration
      (HexFiniteStripBoundaryCore.ofBoundaryData B) where
  mid_complete := E.mid_complete
  boundary_mid_injective := E.boundary_mid_injective
  boundary_classified := E.boundary_classified
  part_unique := by
    intro z hz k l hk hl
    exact E.part_unique z hz k l hk hl
  side_complete := E.side_complete


def hexSmallCellSides (a : ℂ) (h0 : ℤ) : HexContourSides where
  bottom := ∅
  slantPlus := {hexConcreteQ a h0}
  slantMinus := ∅
  top := {hexConcreteR a h0}


noncomputable def hexSmallCellBoundaryCore (a : ℂ) (h0 : ℤ) :
    HexFiniteStripBoundaryCore (hexVBCRegion a h0) h0
      (hexUncondDomain a h0) (hexUncondPairing a h0) where
  sides := hexSmallCellSides a h0
  interior_sub := hexUncond_interior_sub a h0
  vertex_mem := by
    intro v hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    change hexConcreteV a h0 ∈ hexVBC_adjClosure a h0
    unfold hexVBC_adjClosure hexConcreteV
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    simpa using hexVBC_star_mem a (halfStep h0) 1 0 (Or.inl rfl)
  mid_mem := by
    intro e he
    rcases e with ⟨v, j⟩
    change hexUncondMid a h0 j ∈
      ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)
    fin_cases j <;>
      simp [hexUncondMid, hexConcrete_p_eq, hexConcreteQ, hexConcreteR]
  obs_eq := by intro z; rfl
  lam := 0
  tau := hexChi ^ 2
  ups := hexChi ^ 2
  Fa := hexChi
  lam_eq := by
    simp [hexContourLambda, hexSmallCellSides, hexContourSum_empty]
  tau_eq := by
    rw [hexContourTauPlus, hexContourTauMinus]
    simp only [hexSmallCellSides]
    change hexChi ^ 2 =
      hexContourSum (hexVBCRegion a h0).inRegion a h0
          ({hexConcreteQ a h0} : Set ℂ) hexChi
        + hexContourSum (hexVBCRegion a h0).inRegion a h0 ∅ hexChi
    rw [hexVBC_contourSum_singleton_q, hexContourSum_empty, add_zero]
  ups_eq := by
    rw [hexContourUpsilon]
    simp only [hexSmallCellSides]
    exact (hexVBC_contourSum_singleton_r a h0 hexChi).symm
  Fa_eq := by
    change (hexChi : ℂ) = parafObservable (hexVBCRegion a h0).inRegion
      a h0 a (5 / 8) hexChi
    exact (hexVBC_start_observable_eq_hexChi a h0).symm


def hexSmallCellIncidence (j : Fin 3) : HexIncidence (Fin 1) := ⟨0, j⟩

end StatMech.Universality
