/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants
open Filter
open scoped BigOperators Complex Nat


namespace StatMech.FrontierA

noncomputable section

theorem hadamardRootLogTerm_eventuallyEq_partialFractions
    {r : Real} (hr : 0 < r) :
    (hadamardRootLogTerm r) =ᶠ[nhds 0]
      (fun z : Complex =>
        (-Complex.I * (Real.sqrt r : Complex)) *
            ((-Complex.I * (Real.sqrt r : Complex)) * z + 1)⁻¹ +
          (Complex.I * (Real.sqrt r : Complex)) *
            ((Complex.I * (Real.sqrt r : Complex)) * z + 1)⁻¹) := by
  let a : Complex := Real.sqrt r
  have ha2 : a ^ 2 = (r : Complex) := by
    dsimp [a]
    norm_cast
    exact Real.sq_sqrt hr.le
  have hminus : ∀ᶠ z : Complex in nhds 0, (-Complex.I * a) * z + 1 ≠ 0 :=
    (show ContinuousAt (fun z : Complex => (-Complex.I * a) * z + 1) 0 by
      fun_prop).eventually_ne (by simp)
  have hplus : ∀ᶠ z : Complex in nhds 0, (Complex.I * a) * z + 1 ≠ 0 :=
    (show ContinuousAt (fun z : Complex => (Complex.I * a) * z + 1) 0 by
      fun_prop).eventually_ne (by simp)
  filter_upwards [hminus, hplus] with z hzminus hzplus
  change 2 * (r : Complex) * z / (1 + (r : Complex) * z ^ 2) =
    (-Complex.I * a) * ((-Complex.I * a) * z + 1)⁻¹ +
      (Complex.I * a) * ((Complex.I * a) * z + 1)⁻¹
  have hden : 1 + (r : Complex) * z ^ 2 =
      ((-Complex.I * a) * z + 1) * ((Complex.I * a) * z + 1) := by
    rw [← ha2]
    rw [show (-Complex.I * a) * z = -(Complex.I * a * z) by ring,
      show (Complex.I * a) * z = Complex.I * a * z by ring]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hzden : 1 + (r : Complex) * z ^ 2 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hzminus hzplus
  have hzminus' : 1 - a * z * Complex.I ≠ 0 := by
    convert hzminus using 1 <;> ring
  have hzplus' : 1 + a * z * Complex.I ≠ 0 := by
    convert hzplus using 1 <;> ring
  have hzminus'' : -(z * Complex.I * a) + 1 ≠ 0 := by
    convert hzminus using 1 <;> ring
  have hzplus'' : z * Complex.I * a + 1 ≠ 0 := by
    convert hzplus using 1 <;> ring
  apply (div_eq_iff hzden).2
  rw [hden]
  field_simp [hzminus, hzplus, hzminus', hzplus', hzminus'', hzplus'']
  rw [← ha2]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem iteratedDeriv_hadamardRootLogTerm_of_pos
    {r : Real} (hr : 0 < r) (n : Nat) :
    iteratedDeriv n (hadamardRootLogTerm r) 0 =
      (-Complex.I * (Real.sqrt r : Complex)) *
          ((-1 : Complex) ^ n * n ! *
            (-Complex.I * (Real.sqrt r : Complex)) ^ n) +
        (Complex.I * (Real.sqrt r : Complex)) *
          ((-1 : Complex) ^ n * n ! *
            (Complex.I * (Real.sqrt r : Complex)) ^ n) := by
  let a : Complex := Real.sqrt r
  rw [(hadamardRootLogTerm_eventuallyEq_partialFractions hr).iteratedDeriv_eq n]
  change iteratedDeriv n ((fun z : Complex =>
      (-Complex.I * a) * ((-Complex.I * a) * z + 1)⁻¹) +
    (fun z : Complex =>
      (Complex.I * a) * ((Complex.I * a) * z + 1)⁻¹)) 0 = _
  rw [iteratedDeriv_add
    (by fun_prop (disch := norm_num)) (by fun_prop (disch := norm_num))]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  rw [congr_fun (iter_deriv_inv_linear n (-Complex.I * a) 1) 0,
    congr_fun (iter_deriv_inv_linear n (Complex.I * a) 1) 0]
  simp [a]


theorem iteratedDeriv_hadamardRootLogTerm_odd
    (r : Real) (hr : 0 ≤ r) (m : Nat) (hm : 1 ≤ m) :
    iteratedDeriv (2 * m - 1) (hadamardRootLogTerm r) 0 =
      -2 * (-1 : Complex) ^ m * (Nat.factorial (2 * m - 1) : Complex) *
        (r : Complex) ^ m := by
  rcases hr.eq_or_lt with rfl | hr
  · have hzero : hadamardRootLogTerm 0 = (0 : Complex → Complex) := by
      funext z
      simp [hadamardRootLogTerm]
    rw [hzero]
    have hm0 : m ≠ 0 := by omega
    simp [hm0]
  · rw [iteratedDeriv_hadamardRootLogTerm_of_pos hr]
    let a : Complex := Real.sqrt r
    have hs : a ^ 2 = (r : Complex) := by
      dsimp [a]
      norm_cast
      exact Real.sq_sqrt hr.le
    have hn : 2 * m - 1 + 1 = 2 * m := by omega
    have hodd : Odd (2 * m - 1) := by
      use m - 1
      omega
    have hminus : (-Complex.I * a) ^ (2 * m) =
        (-1 : Complex) ^ m * (r : Complex) ^ m := by
      rw [pow_mul]
      have hsq : (-Complex.I * a) ^ 2 = -(a ^ 2) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hsq, neg_pow, hs]
    have hplus : (Complex.I * a) ^ (2 * m) =
        (-1 : Complex) ^ m * (r : Complex) ^ m := by
      rw [pow_mul]
      have hsq : (Complex.I * a) ^ 2 = -(a ^ 2) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hsq, neg_pow, hs]
    change (-Complex.I * a) *
        ((-1 : Complex) ^ (2 * m - 1) * Nat.factorial (2 * m - 1) *
          (-Complex.I * a) ^ (2 * m - 1)) +
      (Complex.I * a) *
        ((-1 : Complex) ^ (2 * m - 1) * Nat.factorial (2 * m - 1) *
          (Complex.I * a) ^ (2 * m - 1)) = _
    rw [hodd.neg_one_pow]
    have hmsucc : (-Complex.I * a) * (-Complex.I * a) ^ (2 * m - 1) =
        (-Complex.I * a) ^ (2 * m) := by
      rw [mul_comm, ← pow_succ, hn]
    have hpsucc : (Complex.I * a) * (Complex.I * a) ^ (2 * m - 1) =
        (Complex.I * a) ^ (2 * m) := by
      rw [mul_comm, ← pow_succ, hn]
    calc
      _ = -(Nat.factorial (2 * m - 1) : Complex) *
          (((-Complex.I * a) * (-Complex.I * a) ^ (2 * m - 1)) +
            ((Complex.I * a) * (Complex.I * a) ^ (2 * m - 1))) := by ring
      _ = -(Nat.factorial (2 * m - 1) : Complex) *
          (((-Complex.I * a) ^ (2 * m)) +
            ((Complex.I * a) ^ (2 * m))) := by rw [hmsucc, hpsucc]
      _ = _ := by rw [hminus, hplus]; ring

theorem iteratedDeriv_hadamardRootLogTerm_one
    (r : Real) (hr : 0 ≤ r) :
    iteratedDeriv 1 (hadamardRootLogTerm r) 0 = 2 * r := by
  simpa using iteratedDeriv_hadamardRootLogTerm_odd r hr 1 (by omega)

theorem iteratedDeriv_hadamardRootLogTerm_three
    (r : Real) (hr : 0 ≤ r) :
    iteratedDeriv 3 (hadamardRootLogTerm r) 0 = -12 * r ^ 2 := by
  convert iteratedDeriv_hadamardRootLogTerm_odd r hr 2 (by omega) using 1 <;>
    norm_num <;> ring

theorem hadamardRootLogTerm_neg (r : Real) (z : Complex) :
    hadamardRootLogTerm r (-z) = -hadamardRootLogTerm r z := by
  unfold hadamardRootLogTerm
  ring

theorem iteratedDeriv_odd_function_of_even
    (f : Complex → Complex) (hf : ∀ z, f (-z) = -f z)
    (order : Nat) (horder : Even order) :
    iteratedDeriv order f 0 = 0 := by
  have hfun : (fun z => f (-z)) = fun z => -f z := funext hf
  have hderiv := congrArg
    (fun g : Complex → Complex => iteratedDeriv order g 0) hfun
  change iteratedDeriv order (fun z => f (-z)) 0 =
    iteratedDeriv order (fun z => -f z) 0 at hderiv
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg,
    horder.neg_one_pow] at hderiv
  simp only [one_smul] at hderiv
  have hself : iteratedDeriv order f 0 =
      -iteratedDeriv order f 0 := by
    simpa using hderiv
  linear_combination hself / 2

theorem iteratedDeriv_hadamardRootLogTerm_even
    (r : Real) (order : Nat) (horder : Even order) :
    iteratedDeriv order (hadamardRootLogTerm r) 0 = 0 :=
  iteratedDeriv_odd_function_of_even (hadamardRootLogTerm r)
    (hadamardRootLogTerm_neg r) order horder

theorem AnalyticOnNhd.iteratedDeriv_local
    {f : Complex → Complex} {U : Set Complex}
    (hf : AnalyticOnNhd Complex f U) (n : Nat) :
    AnalyticOnNhd Complex (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem hasSumLocallyUniformlyOn_iteratedDeriv
    {ι : Type*} {f : ι → Complex → Complex} {g : Complex → Complex}
    {U : Set Complex} (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn f g U)
    (hf : ∀ i, AnalyticOnNhd Complex (f i) U) (n : Nat) :
    HasSumLocallyUniformlyOn
      (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) U := by
  induction n with
  | zero => simpa using hsum
  | succ n ih =>
      rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at ih ⊢
      rw [iteratedDeriv_succ]
      have hder := ih.deriv
        (Filter.Eventually.of_forall fun s =>
          DifferentiableOn.fun_sum fun i _ =>
            (AnalyticOnNhd.iteratedDeriv_local (hf i) n).differentiableOn)
        hU
      apply hder.congr
      intro s z hz
      simp only [Function.comp_apply, iteratedDeriv_succ]
      exact deriv_fun_sum fun i hi =>
        ((AnalyticOnNhd.iteratedDeriv_local (hf i) n).differentiableOn z hz).differentiableAt
          (hU.mem_nhds hz)

theorem summableLocallyUniformlyOn_hadamardRootLogTerm
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) :
    SummableLocallyUniformlyOn (fun n => hadamardRootLogTerm (roots n))
      (hadamardRootNeighborhood roots) := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_hadamardRootNeighborhood roots)
  intro K hKU hcompact
  rcases K.eq_empty_or_nonempty with rfl | hnonempty
  · exact ⟨roots, hsum, by simp⟩
  · obtain ⟨z₀, hz₀, _hmaxEq, hmax⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show ContinuousOn (fun z : Complex => ‖z‖ ^ 2) K by fun_prop)
    let total : Real := ∑' n, roots n
    let gap : Real := 1 - ‖z₀‖ ^ 2 * total
    have hgap : 0 < gap := by
      dsimp [gap, total]
      exact sub_pos.mpr (hKU hz₀)
    let bound : Real := 2 * ‖z₀‖ / gap
    let u : Nat → Real := fun n => roots n * bound
    have hu : Summable u := hsum.mul_right bound
    refine ⟨u, hu, ?_⟩
    intro n z hz
    have hterm : ‖(roots n : Complex) * z ^ 2‖ ≤ ‖z₀‖ ^ 2 * total := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hroots n), norm_pow]
      calc
        roots n * ‖z‖ ^ 2 ≤ roots n * ‖z₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (hmax z hz) (hroots n)
        _ ≤ total * ‖z₀‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (hsum.le_tsum n fun k _ => hroots k) (sq_nonneg ‖z₀‖)
        _ = ‖z₀‖ ^ 2 * total := mul_comm _ _
    have hden : gap ≤ ‖1 + (roots n : Complex) * z ^ 2‖ := by
      calc
        gap = 1 - ‖z₀‖ ^ 2 * total := rfl
        _ ≤ 1 - ‖(roots n : Complex) * z ^ 2‖ := sub_le_sub_left hterm 1
        _ = ‖(1 : Complex)‖ - ‖-((roots n : Complex) * z ^ 2)‖ := by simp
        _ ≤ ‖(1 : Complex) - (-((roots n : Complex) * z ^ 2))‖ :=
          norm_sub_norm_le _ _
        _ = ‖1 + (roots n : Complex) * z ^ 2‖ := by ring_nf
    unfold hadamardRootLogTerm
    rw [norm_div]
    calc
      ‖2 * (roots n : Complex) * z‖ / ‖1 + (roots n : Complex) * z ^ 2‖ ≤
          ‖2 * (roots n : Complex) * z‖ / gap :=
        div_le_div_of_nonneg_left (norm_nonneg _) hgap hden
      _ ≤ ‖2 * (roots n : Complex) * z₀‖ / gap := by
        apply div_le_div_of_nonneg_right _ hgap.le
        have hnormz : ‖z‖ ≤ ‖z₀‖ := by
          nlinarith [hmax z hz, norm_nonneg z, norm_nonneg z₀]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left hnormz
          (mul_nonneg (norm_nonneg 2) (norm_nonneg (roots n : Complex)))
      _ = u n := by
        dsimp [u, bound]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hroots n)]
        norm_num
        field_simp

theorem hadamardRootLogTerm_analyticOnNhd
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (n : Nat) :
    AnalyticOnNhd Complex (hadamardRootLogTerm (roots n))
      (hadamardRootNeighborhood roots) := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_hadamardRootNeighborhood roots)
  intro z hz
  unfold hadamardRootLogTerm
  fun_prop (disch := exact hadamardRootFactor_ne_zero hroots hsum hz n)

theorem hasSum_iteratedDeriv_hadamardRootLogTerm
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) (order : Nat) :
    HasSum
      (fun n => iteratedDeriv order (hadamardRootLogTerm (roots n)) 0)
      (iteratedDeriv order
        (fun z => ∑' n, hadamardRootLogTerm (roots n) z) 0) := by
  have hlocal :=
    (summableLocallyUniformlyOn_hadamardRootLogTerm hroots hsum).hasSumLocallyUniformlyOn
  have hder := hasSumLocallyUniformlyOn_iteratedDeriv
    (isOpen_hadamardRootNeighborhood roots) hlocal
    (hadamardRootLogTerm_analyticOnNhd hroots hsum) order
  exact hder.hasSum (zero_mem_hadamardRootNeighborhood hroots)

theorem summable_root_pow
    {roots : Nat → Real} (hroots : ∀ n, 0 ≤ roots n)
    (hsum : Summable roots) {m : Nat} (hm : 1 ≤ m) :
    Summable fun n => roots n ^ m := by
  let total : Real := ∑' n, roots n
  have htotal : 0 ≤ total := tsum_nonneg hroots
  have hle (n : Nat) : roots n ≤ total :=
    hsum.le_tsum n fun k _ => hroots k
  refine (hsum.mul_right (total ^ (m - 1))).of_nonneg_of_le
    (fun n => pow_nonneg (hroots n) m) ?_
  intro n
  have hm' : m = 1 + (m - 1) := by omega
  have hpow : roots n ^ m = roots n * roots n ^ (m - 1) := by
    calc
      roots n ^ m = roots n ^ (1 + (m - 1)) :=
        congrArg (fun k => roots n ^ k) hm'
      _ = roots n * roots n ^ (m - 1) := by rw [pow_add, pow_one]
  calc
    roots n ^ m = roots n * roots n ^ (m - 1) := hpow
    _ ≤ roots n * total ^ (m - 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hroots n) (hle n) (m - 1)) (hroots n)

theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_rootSum
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) :
    iteratedDeriv order (logDeriv F) 0 =
      iteratedDeriv order
        (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0 := by
  have heq : Set.EqOn (logDeriv F)
      (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z)
      (hadamardRootNeighborhood hF.roots) := by
    intro z hz
    simpa [hadamardRootLogTerm] using hF.logDeriv_eq_tsum hz
  have hevent : (logDeriv F) =ᶠ[nhds 0]
      (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) := by
    filter_upwards
      [(isOpen_hadamardRootNeighborhood hF.roots).mem_nhds
        (zero_mem_hadamardRootNeighborhood hF.roots_nonneg)] with z hz
    exact heq hz
  exact hevent.iteratedDeriv_eq order

theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_even
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) (horder : Even order) :
    iteratedDeriv order (logDeriv F) 0 = 0 := by
  rw [hF.iteratedDeriv_logDeriv_eq_rootSum]
  have hsum := hasSum_iteratedDeriv_hadamardRootLogTerm
    hF.roots_nonneg hF.roots_summable order
  have hzero : HasSum
      (fun _ : Nat => (0 : Complex))
      (iteratedDeriv order
        (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0) :=
    HasSum.congr_fun hsum fun n =>
      (iteratedDeriv_hadamardRootLogTerm_even
        (hF.roots n) order horder).symm
  simpa using hzero.tsum_eq.symm


theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_odd
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (m : Nat) (hm : 1 ≤ m) :
    iteratedDeriv (2 * m - 1) (logDeriv F) 0 =
      -2 * (-1 : Complex) ^ m *
        (Nat.factorial (2 * m - 1) : Complex) *
          (∑' n, hF.roots n ^ m) := by
  rw [hF.iteratedDeriv_logDeriv_eq_rootSum]
  have hsum := hasSum_iteratedDeriv_hadamardRootLogTerm
    hF.roots_nonneg hF.roots_summable (2 * m - 1)
  have hsum' : HasSum
      (fun n => -2 * (-1 : Complex) ^ m *
        (Nat.factorial (2 * m - 1) : Complex) *
          (hF.roots n : Complex) ^ m)
      (iteratedDeriv (2 * m - 1)
        (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0) :=
    HasSum.congr_fun hsum fun n =>
      (iteratedDeriv_hadamardRootLogTerm_odd
        (hF.roots n) (hF.roots_nonneg n) m hm).symm
  rw [← hsum'.tsum_eq]
  rw [tsum_mul_left]
  rw [Complex.ofReal_tsum]
  apply congrArg
  apply tsum_congr
  intro n
  exact (Complex.ofReal_pow (hF.roots n) m).symm


end
end StatMech.FrontierA
