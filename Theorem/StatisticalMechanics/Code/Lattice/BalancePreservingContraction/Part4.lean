/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BalancePreservingContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
import Def.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem bpc_balancePreservingContraction_of_saturating
    (h : bpc_BalanceSaturatingContraction) : BalancePreservingContraction := by
  intro K hK hge a
  by_cases hsat : K ⊆ bpc_orbitFootprint K a
  · exact h K hK hge a hsat
  · 
    rw [Set.not_subset] at hsat
    obtain ⟨c, hcK, hc⟩ := hsat
    exact bpc_contraction_of_not_saturating K hK a c hcK hc


theorem bpc_totalTurn_eq_four_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a
    (bpc_balancePreservingContraction_of_saturating hsat)


theorem bpc_totalTurn_eq_four_value_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  bpc_totalTurn_eq_four_of_saturating K hSK hne a hsat


theorem bpc_domino_cornerBalance : cornerBalance domino dmBase = -4 := by
  rw [cornerBalance_eq_totalTurnZ]
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact domino_totalTurnZ_six


theorem bpc_domino_diff : domino \ {(![1, 0] : Site 2)} = unitCell := by
  ext v
  rw [Set.mem_diff, mem_domino_iff, Set.mem_singleton_iff]
  unfold unitCell
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact h
    · exact absurd h hne
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rw [h]
    intro hcon
    rw [funext_iff, Fin.forall_fin_two] at hcon
    norm_num at hcon


theorem bpc_domino_balanceSaturatingContraction_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
  refine ⟨unitCell, unitCell_finite, ⟨![0, 0], origin_mem_unitCell⟩, ucBase, ?_, ?_⟩
  · 
    have h1 : unitCell.ncard = 1 := by
      unfold unitCell; exact Set.ncard_singleton _
    have h2 : domino.ncard = 2 := by
      unfold domino
      apply Set.ncard_pair
      intro hcon
      rw [funext_iff, Fin.forall_fin_two] at hcon; norm_num at hcon
    omega
  · 
    rw [bpc_domino_cornerBalance, unitCell_cornerBalance ucBase (Or.inl rfl)]


end Lattice
end StatMech
