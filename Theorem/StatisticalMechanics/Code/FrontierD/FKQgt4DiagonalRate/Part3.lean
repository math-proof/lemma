/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionFKG
import Mathlib.Analysis.Subadditive
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4CriticalFreeExactDiagonalRate_tendsto
    {q : Real} (hq : 4 < q) :
    Tendsto (fun n =>
      -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) /
        (n : Real)) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq)) := by
  exact (fkQgt4CriticalFreeExactDiagonalNegLog_subadditive hq).tendsto_lim
    (fkQgt4CriticalFreeExactDiagonalNegLog_bddBelow hq)


theorem tendsto_add_one_div_two_atTop :
    Tendsto (fun n : Nat => (n + 1) / 2) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2 * b)] with n hn
  have hmod := Nat.mod_lt (n + 1) (by decide : 0 < 2)
  have hdecomp := Nat.div_add_mod (n + 1) 2
  omega


theorem tendsto_cast_add_one_div_two_ratio :
    Tendsto (fun n : Nat =>
      (((n + 1) / 2 : Nat) : Real) / (n + 1 : Real))
      atTop (nhds (1 / 2 : Real)) := by
  have hden : Tendsto (fun n : Nat => (n + 1 : Real)) atTop atTop := by
    convert (tendsto_natCast_atTop_atTop (R := Real)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
    funext n
    simp [Function.comp_apply]
  have hinv : Tendsto (fun n : Nat => 1 / (n + 1 : Real))
      atTop (nhds 0) := hden.const_div_atTop 1
  have hlower : ∀ᶠ n : Nat in atTop,
      (1 / 2 : Real) - 1 / (n + 1 : Real) <=
        (((n + 1) / 2 : Nat) : Real) / (n + 1 : Real) := by
    filter_upwards with n
    let N := n + 1
    let k := N / 2
    have hNpos : (0 : Real) < N := by positivity
    have hNne : (N : Real) ≠ 0 := hNpos.ne'
    have hrem := Nat.mod_lt N (by decide : 0 < 2)
    have hdecomp := Nat.div_add_mod N 2
    have hupperNat : N <= 2 * k + 1 := by
      dsimp [k]
      omega
    have hupper : (N : Real) <= 2 * (k : Real) + 1 := by
      exact_mod_cast hupperNat
    dsimp [N, k] at hNpos hupper ⊢
    simp only [Nat.cast_add, Nat.cast_one] at hNpos hupper ⊢
    rw [le_div_iff₀ hNpos]
    field_simp
    nlinarith
  have hupper : ∀ᶠ n : Nat in atTop,
      (((n + 1) / 2 : Nat) : Real) / (n + 1 : Real) <=
        (1 / 2 : Real) := by
    filter_upwards with n
    let N := n + 1
    let k := N / 2
    have hNpos : (0 : Real) < N := by positivity
    have hlowerNat : 2 * k <= N := by
      exact Nat.mul_div_le N 2
    have hlower : 2 * (k : Real) <= (N : Real) := by
      exact_mod_cast hlowerNat
    dsimp [N, k] at hNpos hlower ⊢
    simp only [Nat.cast_add, Nat.cast_one] at hNpos hlower ⊢
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hupper' : ∀ᶠ n : Nat in atTop,
      (((n + 1) / 2 : Nat) : Real) / (n + 1 : Real) <=
        (1 / 2 : Real) - 0 := by
    filter_upwards [hupper] with n hn
    simpa using hn
  have hs := Filter.Tendsto.squeeze'
    (tendsto_const_nhds.sub hinv) tendsto_const_nhds
    hlower hupper'
  simpa using hs

theorem fkQgt4DiagonalSite_eq_exact (n : Nat) :
    fkQgt4DiagonalSite n = fkQgt4ExactDiagonalSite (n / 2) := by
  funext i
  simp [fkQgt4DiagonalSite, fkQgt4ExactDiagonalSite]

theorem fkQgt4CriticalFreeDiagonalTwoPoint_eq_exact
    {q : Real} (hq : 4 < q) (n : Nat) :
    fkQgt4CriticalFreeDiagonalTwoPoint hq n =
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (n / 2) := by
  unfold fkQgt4CriticalFreeDiagonalTwoPoint
    fkQgt4CriticalFreeExactDiagonalTwoPoint
  rw [fkQgt4DiagonalSite_eq_exact]


theorem fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional
    {q : Real} (hq : 4 < q) :
    Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
  let a : Nat -> Real := fun k =>
    -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq k)
  let k : Nat -> Nat := fun n => (n + 1) / 2
  have hrate : Tendsto (fun j => a j / (j : Real)) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq)) := by
    simpa [a] using fkQgt4CriticalFreeExactDiagonalRate_tendsto hq
  have hrateSub : Tendsto (fun n => a (k n) / (k n : Real)) atTop
      (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq)) :=
    hrate.comp tendsto_add_one_div_two_atTop
  have hhalf := tendsto_cast_add_one_div_two_ratio
  have hprod := hrateSub.mul hhalf
  have hevent : ∀ᶠ n : Nat in atTop,
      fkQgt4CriticalFreeDiagonalRate hq n =
        (a (k n) / (k n : Real)) *
          ((k n : Real) / (n + 1 : Real)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hk : k n ≠ 0 := by
      dsimp [k]
      omega
    have hk' : (((n + 1) / 2 : Nat) : Real) ≠ 0 := by
      exact_mod_cast hk
    rw [fkQgt4CriticalFreeDiagonalRate,
      fkQgt4CriticalFreeDiagonalTwoPoint_eq_exact]
    dsimp [a, k]
    field_simp [hk']
  have ht := Filter.Tendsto.congr'
    (Filter.EventuallyEq.symm hevent) hprod
  simpa [div_eq_mul_inv] using ht

theorem fkQgt4CriticalFreeExactDiagonalRateLimit_nonneg
    {q : Real} (hq : 4 < q) :
    0 <= fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq)
  filter_upwards with n
  have hlog := Real.log_nonpos
    (fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq n).le
    (fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one hq n)
  exact div_nonneg (neg_nonneg.mpr hlog) (Nat.cast_nonneg n)

end
end StatMech.FrontierD
