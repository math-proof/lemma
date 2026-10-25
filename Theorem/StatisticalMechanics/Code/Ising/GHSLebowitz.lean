/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsL_ursell_eq_four_duplicate_cov (β h : ℝ) (o x y : V) :
    isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s x)
              * isingExpectation G β h (fun s => spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s y)
              * isingExpectation G β h (fun s => spin s x)
          + 2 * isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x)
              * isingExpectation G β h (fun s => spin s y)
      = 4 * (isingExp2 G β h
              (fun a b => uvar a b o * uvar a b x * tvar a b y)
            - isingExp2 G β h (fun a b => uvar a b o * uvar a b x)
                * isingExp2 G β h (fun a b => tvar a b y)) := by
  have huu := ghsDV_cov2_eq_two_uu G β h o x
  have ht := ghsDV_onePt_eq_tt G β h y
  have hthree :
      (fun a b => uvar a b o * uvar a b x * tvar a b y)
        = (fun a b =>
            (1 / 8 : ℝ) * (spin a o * (spin a x * spin a y))
            + (1 / 8 : ℝ) * ((spin a o * spin a x) * spin b y)
            + (-1 / 8 : ℝ) * ((spin a o * spin a y) * spin b x)
            + (-1 / 8 : ℝ) * (spin a o * (spin b x * spin b y))
            + (-1 / 8 : ℝ) * ((spin a x * spin a y) * spin b o)
            + (-1 / 8 : ℝ) * (spin a x * (spin b o * spin b y))
            + (1 / 8 : ℝ) * (spin a y * (spin b o * spin b x))
            + (1 / 8 : ℝ) * (spin b o * (spin b x * spin b y))) := by
    funext a b
    simp only [uvar, tvar]
    ring
  rw [hthree]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor,
    isingExp2_factor_a, isingExp2_factor_b]
  unfold cov2 at huu
  unfold onePt at ht
  rw [show isingExp2 G β h (fun a b => uvar a b o * uvar a b x) =
      (isingExpectation G β h (fun s => spin s o * spin s x)
        - isingExpectation G β h (fun s => spin s o)
          * isingExpectation G β h (fun s => spin s x)) / 2 by linarith [huu]]
  rw [← ht]
  ring


theorem ghsL_pair_of_duplicate_cov_nonpos (β h : ℝ) (o x y : V)
    (hcov : isingExp2 G β h
              (fun a b => uvar a b o * uvar a b x * tvar a b y)
            ≤ isingExp2 G β h (fun a b => uvar a b o * uvar a b x)
                * isingExp2 G β h (fun a b => tvar a b y)) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  rw [← sub_nonpos]
  rw [ghsThreePoint_eq_ursell, ghsL_ursell_eq_four_duplicate_cov]
  linarith


end Ising
end StatMech
