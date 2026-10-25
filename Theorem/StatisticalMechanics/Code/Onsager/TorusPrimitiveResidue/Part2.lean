/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.TorusPrimitiveResidue.Part2
open scoped BigOperators


namespace StatMech.Onsager

open StatMech.FrontierD

open StatMech.FrontierD.IntegralSquareTorusCycle

noncomputable section

theorem ons_residueOutgoingCoeff_divergence
    {L : Nat} [Fact (2 < L)]
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) :
    ∑ mu : Fin 4, ons_residueOutgoingCoeff C p z mu = 0 := by
  rw [Fin.sum_univ_four]
  simpa [ons_residueOutgoingCoeff] using C.residueCoeff_divergence p z

theorem ons_residueOutgoingCoeff_dartRev
    {L : Nat} [Fact (2 < L)]
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (d : ons_Dart L) :
    ons_residueOutgoingCoeff C p (ons_dartRev L d).1
        (ons_dartRev L d).2 =
      -ons_residueOutgoingCoeff C p d.1 d.2 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [ons_residueOutgoingCoeff, ons_dartRev, ons_dirStep]

theorem ons_residueOutgoingCoeff_eq_zero_of_not_mem
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [NeZero p]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1))
    (z : ZMod L × ZMod L) (mu : Fin 4)
    (hnot : ons_portEdge L (z, mu) ∉ ons_dartEdgeSet v) :
    ons_residueOutgoingCoeff
      (IntegralSquareTorusCycle.ofDarts v hvalid) p z mu = 0 := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  fin_cases mu
  · exact C.residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero p hx z
      (IntegralSquareTorusCycle.ofDarts_horizontal_eq_zero_of_not_mem
        v hvalid z hnot)
  · exact C.residueVerticalCoeff_eq_zero_of_vertical_eq_zero p hy z
      (IntegralSquareTorusCycle.ofDarts_vertical_eq_zero_of_not_mem
        v hvalid z hnot)
  · change -C.residueHorizontalCoeff p (z.1 - 1, z.2) = 0
    rw [neg_eq_zero]
    apply C.residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero p hx
    apply IntegralSquareTorusCycle.ofDarts_horizontal_eq_zero_of_not_mem
    rw [← ons_portEdge_west_eq_horizontal L z]
    exact hnot
  · change -C.residueVerticalCoeff p (z.1, z.2 - 1) = 0
    rw [neg_eq_zero]
    apply C.residueVerticalCoeff_eq_zero_of_vertical_eq_zero p hy
    apply IntegralSquareTorusCycle.ofDarts_vertical_eq_zero_of_not_mem
    rw [← ons_portEdge_south_eq_vertical L z]
    exact hnot


end
end StatMech.Onsager
