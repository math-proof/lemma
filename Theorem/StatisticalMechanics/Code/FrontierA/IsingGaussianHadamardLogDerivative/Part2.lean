/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl.Part2
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem isOpen_hadamardRootNeighborhood (roots : Nat → Real) :
    IsOpen (hadamardRootNeighborhood roots) := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem zero_mem_hadamardRootNeighborhood
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n) :
    (0 : Complex) ∈ hadamardRootNeighborhood roots := by
  have htotal : 0 ≤ ∑' n, roots n := tsum_nonneg hroots
  simp [hadamardRootNeighborhood]

theorem root_le_tsum
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (n : Nat) :
    roots n ≤ ∑' k, roots k := by
  exact hsum.le_tsum n fun k _ => hroots k

theorem hadamardRootFactor_ne_zero
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) (n : Nat) :
    hadamardRootFactor roots n z ≠ 0 := by
  have hterm : ‖(roots n : Complex) * z ^ 2‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hroots n), norm_pow]
    calc
      roots n * ‖z‖ ^ 2 ≤ (∑' k, roots k) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (root_le_tsum hroots hsum n) (sq_nonneg ‖z‖)
      _ = ‖z‖ ^ 2 * (∑' k, roots k) := mul_comm _ _
      _ < 1 := hz
  intro hzero
  have hone : (1 : Complex) = -((roots n : Complex) * z ^ 2) :=
    eq_neg_of_add_eq_zero_left hzero
  have hnorm : (1 : Real) = ‖(roots n : Complex) * z ^ 2‖ := by
    calc
      (1 : Real) = ‖(1 : Complex)‖ := by simp
      _ = ‖-((roots n : Complex) * z ^ 2)‖ := congrArg norm hone
      _ = ‖(roots n : Complex) * z ^ 2‖ := norm_neg _
  linarith

theorem summable_norm_hadamardRootFactor_sub_one
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (z : Complex) :
    Summable fun n => ‖(roots n : Complex) * z ^ 2‖ := by
  have h := hsum.mul_right (‖z‖ ^ 2)
  apply h.congr
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hroots n), norm_pow]

theorem logDeriv_hadamardRootFactor
    (roots : Nat → Real) (n : Nat) (z : Complex) :
    logDeriv (hadamardRootFactor roots n) z =
      2 * (roots n : Complex) * z /
        (1 + (roots n : Complex) * z ^ 2) := by
  unfold hadamardRootFactor
  rw [logDeriv_apply]
  have hp := (hasDerivAt_id z).pow 2
  have hc := hp.const_mul (roots n : Complex)
  have h := hc.const_add 1
  have h' : HasDerivAt
      (fun w : Complex => 1 + (roots n : Complex) * w ^ 2)
      (2 * (roots n : Complex) * z) z := by
    convert h using 1 <;> simp <;> ring
  rw [h'.deriv]

theorem summable_logDeriv_hadamardRootFactor
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) :
    Summable fun n => logDeriv (hadamardRootFactor roots n) z := by
  let total : Real := ∑' n, roots n
  let gap : Real := 1 - ‖z‖ ^ 2 * total
  have hgap : 0 < gap := by
    dsimp [gap, total]
    exact sub_pos.mpr hz
  let bound : Real := 2 * ‖z‖ / gap
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hmajorant : Summable fun n => roots n * bound :=
    hsum.mul_right bound
  apply hmajorant.of_norm_bounded
  intro n
  rw [logDeriv_hadamardRootFactor, norm_div]
  have hterm :
      ‖(roots n : Complex) * z ^ 2‖ ≤ ‖z‖ ^ 2 * total := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hroots n), norm_pow]
    calc
      roots n * ‖z‖ ^ 2 ≤ total * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (root_le_tsum hroots hsum n) (sq_nonneg ‖z‖)
      _ = ‖z‖ ^ 2 * total := mul_comm _ _
  have hden : gap ≤ ‖1 + (roots n : Complex) * z ^ 2‖ := by
    calc
      gap = 1 - ‖z‖ ^ 2 * total := rfl
      _ ≤ 1 - ‖(roots n : Complex) * z ^ 2‖ :=
        sub_le_sub_left hterm 1
      _ = ‖(1 : Complex)‖ - ‖-((roots n : Complex) * z ^ 2)‖ := by simp
      _ ≤ ‖(1 : Complex) - (-((roots n : Complex) * z ^ 2))‖ :=
        norm_sub_norm_le _ _
      _ = ‖1 + (roots n : Complex) * z ^ 2‖ := by ring_nf
  calc
    ‖2 * (roots n : Complex) * z‖ /
        ‖1 + (roots n : Complex) * z ^ 2‖ ≤
        ‖2 * (roots n : Complex) * z‖ / gap :=
      div_le_div_of_nonneg_left (norm_nonneg _) hgap hden
    _ = roots n * bound := by
      dsimp [bound]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hroots n)]
      norm_num
      field_simp

theorem hadamardRootProduct_ne_zero
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) :
    hadamardRootProduct roots z ≠ 0 := by
  unfold hadamardRootProduct hadamardRootFactor
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    exact hadamardRootFactor_ne_zero hroots hsum hz n
  · exact summable_norm_hadamardRootFactor_sub_one hroots hsum z


theorem logDeriv_hadamardRootProduct_eq_tsum
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {z : Complex}
    (hz : z ∈ hadamardRootNeighborhood roots) :
    logDeriv (hadamardRootProduct roots) z =
      ∑' n, 2 * (roots n : Complex) * z /
        (1 + (roots n : Complex) * z ^ 2) := by
  unfold hadamardRootProduct
  rw [logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    (fun n => hadamardRootFactor_ne_zero hroots hsum hz n)
    (fun _ => by unfold hadamardRootFactor; fun_prop)
    (summable_logDeriv_hadamardRootFactor hroots hsum hz)
    (multipliableLocallyUniformlyOn_hadamardRootFactor hroots hsum)
    (hadamardRootProduct_ne_zero hroots hsum hz)]
  apply tsum_congr
  intro n
  exact logDeriv_hadamardRootFactor roots n z


end
end StatMech.FrontierA
