/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ons_lowTempPathSign_eq_spin_mul (config : ConfigSpace V)
    {u v : V} (path : G.Walk u v) :
    ons_lowTempPathSign G config path = spin config u * spin config v := by
  unfold ons_lowTempPathSign
  have hpar := kwd_crossCount_parity config path
  by_cases hsame : config u = config v
  · rw [if_pos (hpar.mpr hsame)]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]
  · rw [if_neg (fun heven => hsame (hpar.mp heven))]
    cases hu : config u <;> cases hv : config v <;>
      simp_all [spin]


theorem isingWeight_eq_lowTempCutWeight (beta : Real)
    (config : ConfigSpace V) :
    isingWeight G beta 0 config =
      Real.exp (beta * G.edgeFinset.card) *
        Real.exp (-2 * beta) ^ (cutEdges G config).card := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [sum_bond_eq_card_sub_two_cut G config, ← Real.exp_nat_mul,
    ← Real.exp_add]
  congr 1
  ring


end StatMech.Onsager
