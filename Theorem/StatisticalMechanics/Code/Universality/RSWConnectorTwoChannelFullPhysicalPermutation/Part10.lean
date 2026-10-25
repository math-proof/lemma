/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalPermConfig_success_of_visibleCutTarget
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hcut : RlcTwoChannelFullPhysicalVisibleCutTargetConnectorSuccess
      gamma gamma' omega) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hcut
  exact ⟨x, y, hx, hy, hxy.mono
    (rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_open
      gamma gamma' omega)⟩

theorem rlc_twoChannelFullVariableConnectorSuccess_of_visibleCutTarget
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hcut : RlcTwoChannelFullPhysicalVisibleCutTargetConnectorSuccess
      gamma gamma' omega) :
    RlcTwoChannelFullVariableConnectorSuccess gamma gamma' omega := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hcut
  exact ⟨x, y, hx, hy, hxy.mono
    (rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_openFullDual
      gamma gamma' omega)⟩


theorem rlc_reachable_between_of_odd_degree_blocks
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R L : V → Prop) [DecidablePred R]
    (hoddSupport : ∀ v, Odd (G.degree v) → R v ∨ L v)
    (hRodd : Odd (Fintype.card {v : V // R v ∧ Odd (G.degree v)})) :
    ∃ r l, R r ∧ L l ∧ G.Reachable r l := by
  classical
  by_contra hno
  let S : Set V := {v | ∃ r, R r ∧ G.Reachable r v}
  have hSL : ∀ {v}, v ∈ S → ¬L v := by
    rintro v ⟨r, hr, hrv⟩ hvL
    exact hno ⟨r, v, hr, hvL, hrv⟩
  have hdegree : ∀ v : S, (G.induce S).degree v = G.degree v := by
    intro v
    apply degree_induce_of_neighborSet_subset
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    obtain ⟨r, hr, hrv⟩ := v.2
    exact ⟨r, hr, hrv.trans hw.reachable⟩
  let oddEquiv :
      {v : S // Odd ((G.induce S).degree v)} ≃
        {v : V // R v ∧ Odd (G.degree v)} :=
    { toFun := fun v => ⟨v.1.1, by
        have hvOdd : Odd (G.degree v.1.1) := by
          rw [← hdegree v.1]
          exact v.2
        refine ⟨?_, hvOdd⟩
        rcases hoddSupport v.1.1 hvOdd with hvR | hvL
        · exact hvR
        · exact (hSL v.1.2 hvL).elim⟩
      invFun := fun v => ⟨⟨v.1, ⟨v.1, v.2.1, Reachable.refl _⟩⟩, by
        rw [hdegree]
        exact v.2.2⟩
      left_inv := fun v => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun v => by
        apply Subtype.ext
        rfl }
  have hEven := SimpleGraph.even_card_odd_degree_vertices (G.induce S)
  rw [← Fintype.card_subtype (fun v : S =>
    Odd ((G.induce S).degree v))] at hEven
  have hcard : Fintype.card {v : S // Odd ((G.induce S).degree v)} =
      Fintype.card {v : V // R v ∧ Odd (G.degree v)} :=
    Fintype.card_congr oddEquiv
  rw [hcard] at hEven
  exact (Nat.not_even_iff_odd.mpr hRodd) hEven


end
end StatMech.Universality
