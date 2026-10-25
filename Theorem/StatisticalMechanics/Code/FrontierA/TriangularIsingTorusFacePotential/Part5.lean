/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part5
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularEvenSubgraph_subset
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L)) :
    F ⊆ (triangularTorusGraph L).edgeFinset := by
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1

theorem triangularZeroHomology_eastCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L) :
    (triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p : ZMod 2) =
      ons_edgeBit F (triangularTorusEastEdge L p) := by
  let E := triangularSquareExpansion L F
  have hE := triangularSquareExpansion_evenSubgraph L F hF
  have hEhom : ons_evenHomology L E = 0 := by
    dsimp [E]
    rw [triangularSquareExpansion_evenHomology L F
      (triangularEvenSubgraph_subset L F hF), hhom]
  rw [triangularFaceEastCoeff_cast_mod_two]
  change (ons_zeroFluxPotential E p +
      (ZMod.finEquiv 2)
        (ons_edgeBit F (triangularTorusNortheastEdge L p))) +
    ons_zeroFluxPotential E (p.1, p.2 - 1) = _
  calc
    _ = (ons_zeroFluxPotential E p +
          ons_zeroFluxPotential E (p.1, p.2 - 1)) +
        (ZMod.finEquiv 2)
          (ons_edgeBit F (triangularTorusNortheastEdge L p)) := by abel
    _ = ons_horizontalZBit E p +
        (ZMod.finEquiv 2)
          (ons_edgeBit F (triangularTorusNortheastEdge L p)) := by
      rw [ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
        L E hE hEhom]
    _ = _ := by
      rw [triangularSquareExpansion_horizontalBit,
        zmodFinEquiv_two_apply]
      let a : ZMod 2 := ons_edgeBit F (triangularTorusEastEdge L p)
      let d : ZMod 2 := ons_edgeBit F (triangularTorusNortheastEdge L p)
      change a + d + d = a
      calc
        _ = a + (d + d) := by abel
        _ = a := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem triangularZeroHomology_northCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L) :
    (triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p : ZMod 2) =
      ons_edgeBit F (triangularTorusNorthEdge L p) := by
  let E := triangularSquareExpansion L F
  have hE := triangularSquareExpansion_evenSubgraph L F hF
  have hEhom : ons_evenHomology L E = 0 := by
    dsimp [E]
    rw [triangularSquareExpansion_evenHomology L F
      (triangularEvenSubgraph_subset L F hF), hhom]
  rw [triangularFaceNorthCoeff_cast_mod_two]
  change (ons_zeroFluxPotential E (p.1 - 1, p.2) +
      (ZMod.finEquiv 2) (ons_edgeBit F
        (triangularTorusNortheastEdge L (p.1 - 1, p.2)))) +
    ons_zeroFluxPotential E p = _
  calc
    _ = (ons_zeroFluxPotential E p +
          ons_zeroFluxPotential E (p.1 - 1, p.2)) +
        (ZMod.finEquiv 2) (ons_edgeBit F
          (triangularTorusNortheastEdge L (p.1 - 1, p.2))) := by abel
    _ = ons_verticalZBit E p +
        (ZMod.finEquiv 2) (ons_edgeBit F
          (triangularTorusNortheastEdge L (p.1 - 1, p.2))) := by
      rw [ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
        L E hE hEhom]
    _ = _ := by
      rw [triangularSquareExpansion_verticalBit,
        zmodFinEquiv_two_apply]
      let a : ZMod 2 := ons_edgeBit F (triangularTorusNorthEdge L p)
      let d : ZMod 2 := ons_edgeBit F
        (triangularTorusNortheastEdge L (p.1 - 1, p.2))
      change a + d + d = a
      calc
        _ = a + (d + d) := by abel
        _ = a := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem triangularZeroHomology_diagonalCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) :
    (triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p : ZMod 2) =
      ons_edgeBit F (triangularTorusNortheastEdge L p) := by
  rw [triangularFaceDiagonalCoeff_cast_mod_two]
  unfold triangularZeroHomologyLowerPotential
  calc
    _ = (triangularZeroHomologyUpperPotential L F p +
        triangularZeroHomologyUpperPotential L F p) +
      (ZMod.finEquiv 2)
        (ons_edgeBit F (triangularTorusNortheastEdge L p)) := by abel
    _ = _ := by
      rw [CharTwo.add_self_eq_zero, zero_add,
        zmodFinEquiv_two_apply]

theorem triangularZeroHomology_eastCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hnot : triangularTorusEastEdge L p ∉ F) :
    triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p = 0 := by
  apply triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
  rw [triangularZeroHomology_eastCoeff_cast L F hF hhom]
  simp [ons_edgeBit, hnot]
  rfl

theorem triangularZeroHomology_northCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hnot : triangularTorusNorthEdge L p ∉ F) :
    triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p = 0 := by
  apply triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
  rw [triangularZeroHomology_northCoeff_cast L F hF hhom]
  simp [ons_edgeBit, hnot]
  rfl

theorem triangularZeroHomology_diagonalCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L)
    (hnot : triangularTorusNortheastEdge L p ∉ F) :
    triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p = 0 := by
  apply triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
  rw [triangularZeroHomology_diagonalCoeff_cast]
  simp [ons_edgeBit, hnot]
  rfl

theorem triangularZeroHomology_eastCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hmem : triangularTorusEastEdge L p ∈ F) :
    triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
  intro hz
  have hcast : (triangularFaceEastCoeff
      (triangularZeroHomologyLowerPotential L F)
      (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = 0 := by
    rw [hz]
    rfl
  rw [triangularZeroHomology_eastCoeff_cast L F hF hhom] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact one_ne_zero hcast

theorem triangularZeroHomology_northCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hmem : triangularTorusNorthEdge L p ∈ F) :
    triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
  intro hz
  have hcast : (triangularFaceNorthCoeff
      (triangularZeroHomologyLowerPotential L F)
      (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = 0 := by
    rw [hz]
    rfl
  rw [triangularZeroHomology_northCoeff_cast L F hF hhom] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact one_ne_zero hcast

theorem triangularZeroHomology_diagonalCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L)
    (hmem : triangularTorusNortheastEdge L p ∈ F) :
    triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
  intro hz
  have hcast : (triangularFaceDiagonalCoeff
      (triangularZeroHomologyLowerPotential L F)
      (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = 0 := by
    rw [hz]
    rfl
  rw [triangularZeroHomology_diagonalCoeff_cast] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact one_ne_zero hcast

end StatMech.FrontierA
