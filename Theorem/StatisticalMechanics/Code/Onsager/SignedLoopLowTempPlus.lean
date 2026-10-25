/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus
open scoped BigOperators
open Finset SimpleGraph MeasureTheory


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls


theorem sum_bond_finset_eq_card_sub_two_cut {V : Type*}
    (B : Finset (Sym2 V)) (config : ConfigSpace V) :
    (∑ edge ∈ B, bond config edge) =
      (B.card : Real) - 2 * (ons_fvCutEdges B config).card := by
  classical
  unfold ons_fvCutEdges
  rw [← Finset.sum_filter_add_sum_filter_not B
    (fun edge => bond config edge = -1)]
  have hneg :
      (∑ edge ∈ B.filter (fun edge => bond config edge = -1),
        bond config edge) =
        -(B.filter (fun edge => bond config edge = -1)).card := by
    rw [Finset.sum_congr rfl
      (fun edge hedge => (Finset.mem_filter.mp hedge).2)]
    simp
  have hpos :
      (∑ edge ∈ B.filter (fun edge => ¬ (bond config edge = -1)),
        bond config edge) =
        (B.filter (fun edge => ¬ (bond config edge = -1))).card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : Real))]
    · simp
    intro edge hedge
    rcases bond_eq_one_or_neg_one config edge with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp hedge).2
  rw [hneg, hpos]
  have hcard :
      (B.filter (fun edge => bond config edge = -1)).card +
        (B.filter (fun edge => ¬ (bond config edge = -1))).card = B.card :=
    Finset.card_filter_add_card_filter_not _
  push_cast [← hcard]
  ring


theorem fvWeight_zero_eq_lowTempCutWeight
    (d n : Nat) (eta : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (beta : Real)
    (tau : {x // x ∈ box d n} → Bool) :
    fvWeight eta n B beta 0 tau =
      Real.exp (beta * B.card) *
        Real.exp (-2 * beta) ^ (ons_fvCutEdges B (glue eta tau)).card := by
  unfold fvWeight fvEnergy
  simp only [zero_mul, sub_zero]
  rw [sum_bond_finset_eq_card_sub_two_cut, ← Real.exp_nat_mul,
    ← Real.exp_add]
  congr 1
  ring


end StatMech.Onsager
