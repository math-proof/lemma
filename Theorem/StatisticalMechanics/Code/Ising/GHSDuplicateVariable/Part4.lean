/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSDuplicateVariable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Def.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsDV_cov2_eq_two_uu (β h : ℝ) (o x : V) :
    cov2 G β h o x = 2 * isingExp2 G β h (fun a b => uvar a b o * uvar a b x) := by
  have hexp : (fun a b => uvar a b o * uvar a b x)
      = (fun a b =>
          (1/4 : ℝ) * (spin a o * spin a x)
          + (-1/4 : ℝ) * (spin a o * spin b x)
          + (-1/4 : ℝ) * (spin a x * spin b o)
          + (1/4 : ℝ) * (spin b o * spin b x)) := by
    funext a b; simp only [uvar]; ring
  rw [hexp]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor,
    isingExp2_factor_a, isingExp2_factor_b]
  unfold cov2
  ring


theorem ghsDV_uu_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    0 ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x) := by
  have hc := cov2_nonneg G β h hβ hh o x hox
  rw [ghsDV_cov2_eq_two_uu] at hc
  linarith


theorem ghsDV_onePt_eq_tt (β h : ℝ) (o : V) :
    onePt G β h o = isingExp2 G β h (fun a b => tvar a b o) := by
  have hexp : (fun a b => tvar a b o)
      = (fun a b => (1/2 : ℝ) * spin a o + (1/2 : ℝ) * spin b o) := by
    funext a b; simp only [tvar]; ring
  rw [hexp]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor_a, isingExp2_factor_b]
  unfold onePt
  ring


theorem ghsDV_tt_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ isingExp2 G β h (fun a b => tvar a b o) := by
  have hsp : (0 : ℝ) ≤ onePt G β h o := expectation_spin_nonneg G β h hβ hh o
  rwa [ghsDV_onePt_eq_tt] at hsp


theorem ghsDV_of_three_replica_nonneg (β h : ℝ) (o : V)
    (hsign : ∀ e ∈ G.edgeFinset, ∀ x y : V, e = s(x, y) →
      0 ≤ isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)) :
    GHSThreePointSym G β h o := by
  intro e he
  induction e with
  | h x y =>
    exact (ghsDV_ghs_iff_three_replica_nonneg G β h o x y).mpr (hsign _ he x y rfl)

end Ising
end StatMech
