import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Section8Example4Integrable


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[f_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
lemma f_neg_one
  {x : ℂ}
-- given
  (h : (-1 : ℤ) ≤ -1) :
-- imply
  f ⟨-1, h⟩ x = 1 := by
-- proof
  simp [f]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[f_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
lemma f_natCast
  {k : ℕ}
  {x : ℂ}
-- given
  (h : (-1 : ℤ) ≤ k) :
-- imply
  f ⟨k, h⟩ x = generalizedBellGenerating 0 1 x k := by
-- proof
  have hk : (k : ℤ) ≠ -1 := by omega
  simp [f, hk]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[real_pow_le_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma real_pow_le_aux (k j : ℕ) : ((j : ℝ) + 1) ^ k ≤ ((2 ^ k : ℕ) : ℝ) ^ j := by
  have hle : ((j : ℝ) + 1) ≤ (2 ^ j : ℕ) := by
    have h : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h2 ⊢
    linarith
  calc ((j : ℝ) + 1) ^ k ≤ ((2 ^ j : ℕ) : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) hle k
    _ = (((2 : ℝ) ^ j) ^ k) := by push_cast; ring_nf
    _ = (((2 : ℝ) ^ k) ^ j) := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (((2 ^ k : ℕ) : ℝ) ^ j) := by push_cast; ring_nf

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[summable_bound_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma summable_bound_aux (k : ℕ) (R : ℝ) (hR : 0 ≤ R) :
  Summable (fun j : ℕ => ((j : ℝ) + 1) ^ k * R ^ (j + 1) / (Nat.factorial j : ℝ)) := by
  have hbase : Summable (fun j : ℕ => R * (((2 ^ k : ℕ) : ℝ) * R) ^ j / (Nat.factorial j : ℝ)) := by
    have h := Real.summable_pow_div_factorial (((2 ^ k : ℕ) : ℝ) * R)
    have := h.mul_left R
    simpa [mul_div_assoc, mul_comm, mul_left_comm] using this
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hbase
  intro j
  have hle := real_pow_le_aux k j
  have hfact : (0 : ℝ) ≤ (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hRpow : (0 : ℝ) ≤ R ^ (j + 1) := pow_nonneg hR _
  have h2 : ((j : ℝ) + 1) ^ k * R ^ (j + 1) / (Nat.factorial j : ℝ)
    ≤ ((2 ^ k : ℕ) : ℝ) ^ j * R ^ (j + 1) / (Nat.factorial j : ℝ) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle hRpow) hfact
  calc ((j : ℝ) + 1) ^ k * R ^ (j + 1) / (Nat.factorial j : ℝ)
    ≤ ((2 ^ k : ℕ) : ℝ) ^ j * R ^ (j + 1) / (Nat.factorial j : ℝ) := h2
    _ = R * (((2 ^ k : ℕ) : ℝ) * R) ^ j / (Nat.factorial j : ℝ) := by
      rw [mul_pow, pow_succ']
      ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[cont_each_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma cont_each_aux (k : ℕ) (x : ℂ) (j : ℕ) :
  Continuous (fun t : ℝ => (↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) /
    (↑(Nat.factorial j) : ℂ)) := by
  apply Continuous.div_const
  apply Continuous.mul continuous_const
  apply Continuous.pow
  apply Continuous.mul Complex.continuous_ofReal continuous_const

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[norm_bound_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
private lemma norm_bound_aux (k : ℕ) (x : ℂ) (j : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
  ‖(↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) / (↑(Nat.factorial j) : ℂ)‖
    ≤ ((j : ℝ) + 1) ^ k * ‖x‖ ^ (j + 1) / (Nat.factorial j : ℝ) := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have habs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht0]; exact ht1
  have hR : 0 ≤ ‖x‖ := norm_nonneg _
  have hcoeff : ‖(↑((j + 1) ^ k : ℕ) : ℂ)‖ = ((j : ℝ) + 1) ^ k := by
    rw [Complex.norm_natCast]
    push_cast
    ring
  have hfactC : ‖(↑(Nat.factorial j) : ℂ)‖ = (Nat.factorial j : ℝ) := by
    rw [Complex.norm_natCast]
  have hy : ‖((t : ℂ) * x)‖ ≤ ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖x‖ ≤ 1 * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right habs hR
      _ = ‖x‖ := one_mul _
  have hyPow : ‖(((t : ℂ) * x) ^ (j + 1))‖ ≤ ‖x‖ ^ (j + 1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hy _
  rw [norm_div, norm_mul, hcoeff, hfactC]
  have hfact_nonneg : (0 : ℝ) ≤ (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hmul : ((j : ℝ) + 1) ^ k * ‖(((t : ℂ) * x) ^ (j + 1))‖
    ≤ ((j : ℝ) + 1) ^ k * ‖x‖ ^ (j + 1) := by
    exact mul_le_mul_of_nonneg_left hyPow (by positivity)
  exact div_le_div_of_nonneg_right hmul hfact_nonneg
set_option backward.proofsInPublic true in

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable

/--
[ramanujan_part1_ch3_section8_example4_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean)
-/
@[path]
lemma ramanujan_part1_ch3_section8_example4_integrable
  {m : ℕ}
  {x : ℂ} :
-- imply
  IntervalIntegrable (fun t : ℝ => x * f ⟨(m : ℤ) - 1,
    by omega⟩ ((t : ℂ) * x)) MeasureTheory.volume 0 1 := by
-- proof
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  cases m with
  | zero =>
    have hn : (⟨((0 : ℕ) : ℤ) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val = -1 := by
      simp
    have hfun : (fun t : ℝ => x * f ⟨((0 : ℕ) : ℤ) - 1, by omega⟩ ((t : ℂ) * x))
      = (fun _ : ℝ => x * 1) := by
      funext t
      simp [f]
    rwa [hfun]
  | succ k =>
    have hval : (⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val = (k : ℤ) := by
      push_cast
      ring
    have hn_ne : (⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val ≠ -1 := by
      rw [hval]
      omega
    have htoNat : (⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ : { n : ℤ // -1 ≤ n }).val.toNat = k := by
      rw [hval]
      exact Int.toNat_natCast k
    have hfun : (fun t : ℝ => x * f ⟨(((k + 1 : ℕ) : ℤ)) - 1, by omega⟩ ((t : ℂ) * x))
      = (fun t : ℝ => x * (Complex.exp (-((t : ℂ) * x)) *
        ∑' (j : ℕ), (↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) /
          (↑(Nat.factorial j) : ℂ))) := by
      funext t
      simp [f, generalizedBellGenerating]
    rw [hfun]
    have hS : ContinuousOn
      (fun t : ℝ => ∑' (j : ℕ), (↑((j + 1) ^ k : ℕ) : ℂ) * (((t : ℂ) * x) ^ (j + 1)) /
        (↑(Nat.factorial j) : ℂ)) (Set.Icc 0 1) := by
      apply continuousOn_tsum (fun j => (cont_each_aux k x j).continuousOn)
        (summable_bound_aux k ‖x‖ (norm_nonneg _))
      intro j t ht
      exact norm_bound_aux k x j t ht
    have hexp : ContinuousOn (fun t : ℝ => Complex.exp (-((t : ℂ) * x))) (Set.Icc 0 1) := by
      apply Continuous.continuousOn
      fun_prop
    exact continuousOn_const.mul (hexp.mul hS)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Section8Example4Integrable


-- created on 2026-10-20
-- updated on 2026-10-26
