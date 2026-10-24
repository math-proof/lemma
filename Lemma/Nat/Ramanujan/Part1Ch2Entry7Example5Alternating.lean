import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[arctan_ne_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma arctan_ne_odd (x : ℝ) (k : ℤ) :
  Real.arctan x ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 := by
  intro h
  have hlt := Real.arctan_lt_pi_div_two x
  have hgt := Real.neg_pi_div_two_lt_arctan x
  rw [h] at hlt hgt
  have hpi : (0 : ℝ) < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have e1 : (2 : ℝ) * (k : ℝ) + 1 < 1 := by
    have h' : ((2 : ℝ) * (k : ℝ) + 1) * (Real.pi / 2) < 1 * (Real.pi / 2) := by
      linear_combination hlt
    exact lt_of_mul_lt_mul_right h' (le_of_lt hpi)
  have e2 : (-1 : ℝ) < (2 : ℝ) * (k : ℝ) + 1 := by
    have h'' : (-1 : ℝ) * (Real.pi / 2) < ((2 : ℝ) * (k : ℝ) + 1) * (Real.pi / 2) := by
      linear_combination hgt
    exact lt_of_mul_lt_mul_right h'' (le_of_lt hpi)
  have h1 : (2 * k + 1 : ℤ) < 1 := by
    have : (((2 * k + 1 : ℤ)) : ℝ) < ((1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have h2 : (-1 : ℤ) < 2 * k + 1 := by
    have : (((-1 : ℤ)) : ℝ) < (((2 * k + 1 : ℤ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  omega

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[arctan_sub_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma arctan_sub_of_nonneg {x y : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y) (h : y ≤ x) :
  Real.arctan x - Real.arctan y = Real.arctan ((x - y) / (1 + x * y)) := by
  have htan : Real.tan (Real.arctan x - Real.arctan y) = (x - y) / (1 + x * y) := by
    rw [Real.tan_sub (Or.inl ⟨fun k => arctan_ne_odd x k, fun k => arctan_ne_odd y k⟩),
      Real.tan_arctan, Real.tan_arctan]
  have hle : Real.arctan y ≤ Real.arctan x := Real.arctan_le_arctan_iff.mpr h
  have hnn : (0 : ℝ) ≤ Real.arctan y := Real.arctan_nonneg.mpr hy
  have hlt := Real.arctan_lt_pi_div_two x
  have hpi : (0 : ℝ) < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have hhi : Real.arctan x - Real.arctan y < Real.pi / 2 := by linarith
  have hlo : -(Real.pi / 2) < Real.arctan x - Real.arctan y := by linarith
  have hmain := Real.arctan_tan hlo hhi
  rwa [htan] at hmain

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[arctan_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma arctan_key (n : ℕ) :
  Real.arctan (2 / (((n : ℝ) + 1) ^ 2)) = Real.arctan ((n : ℝ) + 2) - Real.arctan (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h := arctan_sub_of_nonneg (x := (n : ℝ) + 2) (y := (n : ℝ)) (by linarith) hn (by linarith)
  rw [h]
  congr 1
  have hne1 : (((n : ℝ) + 1) ^ 2) ≠ 0 := by positivity
  have hne2 : (1 + ((n : ℝ) + 2) * (n : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[partial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma partial_sum (N : ℕ) :
  ∑ n ∈ Finset.range N, ((-1 : ℝ) ^ n * Real.arctan ((2 : ℝ) / (((n : ℝ) + 1) ^ 2)))
  = Real.pi / 4 + (-1 : ℝ) ^ N * (Real.arctan ((N : ℝ)) - Real.arctan ((N : ℝ) + 1)) := by
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero, pow_zero, one_mul, Nat.cast_zero, zero_add,
      Real.arctan_zero, Real.arctan_one]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, arctan_key k, pow_succ]
    push_cast
    ring_nf

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[hsumm_base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma hsumm_base : Summable (fun m : ℕ => (2 : ℝ) / ((m : ℝ) ^ 2)) := by
  have hbase : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hmul := hbase.mul_left 2
  refine hmul.congr (fun m => ?_)
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[hsumm_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma hsumm_shift : Summable (fun n : ℕ => (2 : ℝ) / ((((n : ℝ)) + 1) ^ 2)) := by
  have hshift := (summable_nat_add_iff (f := fun m : ℕ => (2 : ℝ) / ((m : ℝ) ^ 2)) 1).mpr hsumm_base
  refine hshift.congr (fun n => ?_)
  push_cast
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[hsumm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma hsumm : Summable (fun n : ℕ => (-1 : ℝ) ^ n * Real.arctan ((2 : ℝ) / (((n : ℝ) + 1) ^ 2))) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (2 : ℝ) / ((((n : ℝ)) + 1) ^ 2)) hsumm_shift
  intro n
  have hnn : (0 : ℝ) ≤ (2 : ℝ) / ((((n : ℝ)) + 1) ^ 2) := by positivity
  have h1 : ‖(-1 : ℝ) ^ n‖ = 1 := by simp
  rw [norm_mul, h1, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.arctan_nonneg.mpr hnn)]
  exact Real.arctan_le_self hnn

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[err_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma err_eq (N : ℕ) :
  ‖(-1 : ℝ) ^ N * (Real.arctan ((N : ℝ)) - Real.arctan ((N : ℝ) + 1))‖
  = Real.arctan ((N : ℝ) + 1) - Real.arctan ((N : ℝ)) := by
  have hle : Real.arctan ((N : ℝ)) ≤ Real.arctan ((N : ℝ) + 1) :=
    Real.arctan_le_arctan_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have h1 : ‖(-1 : ℝ) ^ N‖ = 1 := by simp
  rw [norm_mul, h1, one_mul, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hle)]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[err_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma err_tendsto : Filter.Tendsto
  (fun N : ℕ => (-1 : ℝ) ^ N * (Real.arctan ((N : ℝ)) - Real.arctan ((N : ℝ) + 1)))
  Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (1 : ℝ) / (((N : ℝ)) + 1))
  · intro N
    have hu : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hsub := arctan_sub_of_nonneg (x := (N : ℝ) + 1) (y := (N : ℝ))
      (by linarith) hu (by linarith)
    have harg : ((N : ℝ) + 1 - (N : ℝ)) / (1 + ((N : ℝ) + 1) * (N : ℝ))
      ≤ 1 / ((N : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
      have h3 : ((N : ℝ) + 1 - (N : ℝ)) = 1 := by ring
      rw [h3]
      apply one_div_le_one_div_of_le h1 _
      nlinarith [sq_nonneg (N : ℝ)]
    have hnn : (0 : ℝ) ≤ ((N : ℝ) + 1 - (N : ℝ)) / (1 + ((N : ℝ) + 1) * (N : ℝ)) := by
      have h3 : ((N : ℝ) + 1 - (N : ℝ)) = 1 := by ring
      rw [h3]
      positivity
    calc ‖(-1 : ℝ) ^ N * (Real.arctan ((N : ℝ)) - Real.arctan ((N : ℝ) + 1))‖
      = Real.arctan ((N : ℝ) + 1) - Real.arctan ((N : ℝ)) := err_eq N
      _ = Real.arctan (((N : ℝ) + 1 - (N : ℝ)) / (1 + ((N : ℝ) + 1) * (N : ℝ))) := hsub
      _ ≤ ((N : ℝ) + 1 - (N : ℝ)) / (1 + ((N : ℝ) + 1) * (N : ℝ)) :=
        Real.arctan_le_self hnn
      _ ≤ 1 / ((N : ℝ) + 1) := harg
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating

/--
[ramanujan_part1_ch2_entry7_example5_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry7_example5_alternating
  :
-- imply
  HasSum (fun n : ℕ => (-1 : ℝ) ^ n * Real.arctan ((2 : ℝ) / (((n : ℝ) + 1) ^ 2))) (Real.pi / 4) := by
-- proof
  apply (hsumm.hasSum_iff_tendsto_nat).mpr
  have hfun : (fun n : ℕ => ∑ i ∈ Finset.range n,
    (-1 : ℝ) ^ i * Real.arctan ((2 : ℝ) / (((i : ℝ) + 1) ^ 2)))
    = (fun n : ℕ => Real.pi / 4 + (-1 : ℝ) ^ n * (Real.arctan ((n : ℝ)) - Real.arctan ((n : ℝ) + 1))) :=
    funext partial_sum
  rw [hfun]
  have hlim : Filter.Tendsto
    (fun n : ℕ => Real.pi / 4 + (-1 : ℝ) ^ n * (Real.arctan ((n : ℝ)) - Real.arctan ((n : ℝ) + 1)))
    Filter.atTop (nhds (Real.pi / 4 + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds err_tendsto
  simpa using hlim

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating


-- created on 2026-10-20
-- updated on 2026-10-23
