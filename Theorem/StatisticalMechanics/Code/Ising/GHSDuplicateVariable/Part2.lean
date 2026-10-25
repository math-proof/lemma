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
import Def.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] lemma dvar_apply (a b c : ConfigSpace V) (w : V) :
    dvar a b c w = spin b w + spin c w - 2 * spin a w := rfl


theorem isingExp3_eq_iterated (β h : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h F
      = isingExpectation G β h
          (fun a => isingExpectation G β h
            (fun b => isingExpectation G β h (fun c => F a b c))) := by
  unfold isingExp3 isingExpectation
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring


theorem isingExp3_finset_sum (β h : ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → ConfigSpace V → ConfigSpace V → ConfigSpace V → ℝ) :
    isingExp3 G β h (fun a b c => ∑ i ∈ s, F i a b c)
      = ∑ i ∈ s, isingExp3 G β h (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [isingExp3]
  | @insert j s hj IH =>
    have hrw : (fun a b c => ∑ i ∈ insert j s, F i a b c)
        = (fun a b c => F j a b c + ∑ i ∈ s, F i a b c) := by
      funext a b c; rw [Finset.sum_insert hj]
    rw [hrw, isingExp3_add, IH, Finset.sum_insert hj]


theorem ghsDV_three_replica_expand (β h : ℝ) (o x y : V) :
    isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)
      = (-6) * (isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s x)
              * isingExpectation G β h (fun s => spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s y)
              * isingExpectation G β h (fun s => spin s x)
          + 2 * isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x)
              * isingExpectation G β h (fun s => spin s y)) := by
  have hexp : (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y)
      = (fun a b c =>
          (1:ℝ) * ((spin b o * (spin b x * (spin b y))))
          + (1:ℝ) * ((spin b o * (spin b x)) * (spin c y))
          + (-2:ℝ) * ((spin a y) * (spin b o * (spin b x)))
          + (1:ℝ) * ((spin b o * (spin b y)) * (spin c x))
          + (1:ℝ) * ((spin b o) * (spin c x * (spin c y)))
          + (-2:ℝ) * ((spin a y) * (spin b o) * (spin c x))
          + (-2:ℝ) * ((spin a x) * (spin b o * (spin b y)))
          + (-2:ℝ) * ((spin a x) * (spin b o) * (spin c y))
          + (4:ℝ) * ((spin a x * (spin a y)) * (spin b o))
          + (1:ℝ) * ((spin b x * (spin b y)) * (spin c o))
          + (1:ℝ) * ((spin b x) * (spin c o * (spin c y)))
          + (-2:ℝ) * ((spin a y) * (spin b x) * (spin c o))
          + (1:ℝ) * ((spin b y) * (spin c o * (spin c x)))
          + (1:ℝ) * ((spin c o * (spin c x * (spin c y))))
          + (-2:ℝ) * ((spin a y) * (spin c o * (spin c x)))
          + (-2:ℝ) * ((spin a x) * (spin b y) * (spin c o))
          + (-2:ℝ) * ((spin a x) * (spin c o * (spin c y)))
          + (4:ℝ) * ((spin a x * (spin a y)) * (spin c o))
          + (-2:ℝ) * ((spin a o) * (spin b x * (spin b y)))
          + (-2:ℝ) * ((spin a o) * (spin b x) * (spin c y))
          + (4:ℝ) * ((spin a o * (spin a y)) * (spin b x))
          + (-2:ℝ) * ((spin a o) * (spin b y) * (spin c x))
          + (-2:ℝ) * ((spin a o) * (spin c x * (spin c y)))
          + (4:ℝ) * ((spin a o * (spin a y)) * (spin c x))
          + (4:ℝ) * ((spin a o * (spin a x)) * (spin b y))
          + (4:ℝ) * ((spin a o * (spin a x)) * (spin c y))
          + (-8:ℝ) * ((spin a o * (spin a x * (spin a y))))
          ) := by
    funext a b c; simp only [dvar_apply]; ring
  rw [hexp]
  simp only [isingExp3_add, isingExp3_const_mul, isingExp3_factor,
    isingExp3_factor_a, isingExp3_factor_b, isingExp3_factor_c,
    isingExp3_factor_ab, isingExp3_factor_ac, isingExp3_factor_bc]
  ring


theorem ghsDV_ursell_eq_three_replica (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y)
      = (-(1/6)) * isingExp3 G β h
          (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) := by
  rw [ghsThreePoint_eq_ursell, ghsDV_three_replica_expand]
  ring


theorem ghsDV_ghs_iff_three_replica_nonneg (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y)
      ↔ 0 ≤ isingExp3 G β h (fun a b c => dvar a b c o * dvar a b c x * dvar a b c y) := by
  have hid := ghsDV_ursell_eq_three_replica G β h o x y
  rw [← sub_nonneg (a := ghsBoundSym G β h o s(x, y))]
  constructor
  · intro hle; nlinarith [hle, hid]
  · intro hge; nlinarith [hge, hid]


end Ising
end StatMech
