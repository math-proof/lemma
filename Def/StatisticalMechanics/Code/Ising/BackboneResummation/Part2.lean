/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def bbr_allFilter (M : Finset (Current V)) (o x y : V) : Finset (Current V) :=
  M.filter (fun m => hnw_allConn G m o x y)


noncomputable def bbr_noneFilter (M : Finset (Current V)) (o x y : V) : Finset (Current V) :=
  M.filter (fun m => hnw_noneConn G m o x y)


def bbr_BackboneSurgery (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (A : Finset V)
    (o x y : V) : Prop :=
  ∃ Ψ : Current V → Current V,
    (∀ m ∈ bbr_allFilter G M o x y, Ψ m ∈ bbr_noneFilter G M o x y)
    ∧ (∀ m ∈ bbr_allFilter G M o x y, ∀ m' ∈ bbr_allFilter G M o x y, Ψ m = Ψ m' → m = m')
    ∧ (∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m A ≤ hnw_mass G β J (Ψ m) A)


end Ising
end StatMech
