/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


noncomputable def hexSmallCellCoreOrientation (a : ℂ) :
    HexFiniteStripCoreOrientation (hexSmallCellBoundaryCore a 1) where
  heading := fun _ j => hexSmallCellHeading 1 j
  hgeom := hexSmallCell_hgeom a 1
  startIncidence := hexSmallCellIncidence 0
  startFiber_singleton := by
    let E := hexSmallCellCoreEnumeration a 1
    obtain ⟨eA, hfiber⟩ := E.exists_startIncidence
    have heAin : eA ∈ hexFiniteStripPhysicalStartFiber
        (R := hexVBCRegion a 1) (hexUncondPairing a 1) := by
      rw [hfiber]
      simp
    obtain ⟨heA, hmidA⟩ := Finset.mem_filter.mp heAin
    have he0 := hexSmallCellIncidence_boundary_mem a 1 0
    have hmid0 : (hexUncondDomain a 1).mid
        (hexSmallCellIncidence 0).vtx (hexSmallCellIncidence 0).edge =
        (hexVBCRegion a 1).start := by
      change hexConcreteV a 1 + hexConcreteDu a 1 = a
      exact hexConcrete_p_eq a 1
    have heq : eA = hexSmallCellIncidence 0 :=
      E.boundary_mid_injective eA heA (hexSmallCellIncidence 0) he0
        (hmidA.trans hmid0.symm)
    rw [← heq]
    exact hfiber
  start_mid := by
    change hexConcreteV a 1 + hexConcreteDu a 1 = a
    exact hexConcrete_p_eq a 1
  start_heading := by norm_num [hexSmallCellIncidence, hexSmallCellHeading]
  headL := 4
  headTp := 6
  headTm := 4
  headU := 8
  hHeadL := by
    intro e he hm
    simp [hexSmallCellBoundaryCore, hexSmallCellSides] at hm
  hHeadTp := by
    intro e he hm
    have hmid : (hexUncondDomain a 1).mid e.vtx e.edge =
        (hexUncondDomain a 1).mid (hexSmallCellIncidence 1).vtx
          (hexSmallCellIncidence 1).edge := by
      simpa [hexSmallCellBoundaryCore, hexSmallCellSides,
        hexSmallCellIncidence, hexUncondDomain, hexUncondMid] using hm
    have heq := (hexSmallCellCoreEnumeration a 1).boundary_mid_injective
      e he (hexSmallCellIncidence 1)
        (hexSmallCellIncidence_boundary_mem a 1 1) hmid
    subst e
    norm_num [hexSmallCellIncidence, hexSmallCellHeading]
  hHeadTm := by
    intro e he hm
    simp [hexSmallCellBoundaryCore, hexSmallCellSides] at hm
  hHeadU := by
    intro e he hm
    have hmid : (hexUncondDomain a 1).mid e.vtx e.edge =
        (hexUncondDomain a 1).mid (hexSmallCellIncidence 2).vtx
          (hexSmallCellIncidence 2).edge := by
      simpa [hexSmallCellBoundaryCore, hexSmallCellSides,
        hexSmallCellIncidence, hexUncondDomain, hexUncondMid] using hm
    have heq := (hexSmallCellCoreEnumeration a 1).boundary_mid_injective
      e he (hexSmallCellIncidence 2)
        (hexSmallCellIncidence_boundary_mem a 1 2) hmid
    subst e
    norm_num [hexSmallCellIncidence, hexSmallCellHeading]


end StatMech.Universality
