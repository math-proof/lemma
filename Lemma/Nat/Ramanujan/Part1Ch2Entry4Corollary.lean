import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry4Corollary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry4Corollary


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[H_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma H_zero : H 0 = 0 := by
simp [H, harmonic_zero]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[H_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma H_succ (m : ℕ) : H (m+1) = H m + 1/((m:ℝ)+1) := by
  simp only [H]
  have h := harmonic_succ m
  have h2 : ((harmonic (m+1) : ℚ) : ℝ) = ((harmonic m : ℚ) : ℝ) + ((((m+1 : ℕ) : ℚ))⁻¹ : ℚ) := by
    rw [h]
    push_cast
    ring
  rw [h2]
  congr 1
  push_cast
  rw [inv_eq_one_div]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[term_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma term_eq (n : ℕ) (hn : 1 ≤ n) :
  (2:ℝ)/((4*(n:ℝ))^3 - 4*(n:ℝ))
    = -1/(2*(n:ℝ)) + 1/(4*(n:ℝ)-1) + 1/(4*(n:ℝ)+1) := by
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h4npos : (0:ℝ) < 4*(n:ℝ) := by linarith
  have h4n : (4*(n:ℝ)) ≠ 0 := ne_of_gt h4npos
  have h1 : (4*(n:ℝ)-1) ≠ 0 := by
    have h : (0:ℝ) < 4*(n:ℝ)-1 := by linarith
    exact ne_of_gt h
  have h2 : (4*(n:ℝ)+1) ≠ 0 := by
    have h : (0:ℝ) < 4*(n:ℝ)+1 := by linarith
    exact ne_of_gt h
  have h2n : (2*(n:ℝ)) ≠ 0 := by
    have h : (0:ℝ) < 2*(n:ℝ) := by linarith
    exact ne_of_gt h
  have h12 : ((4*(n:ℝ)-1)*(4*(n:ℝ)+1)) ≠ 0 := mul_ne_zero h1 h2
  have e : (1:ℝ)/(4*(n:ℝ)-1) + 1/(4*(n:ℝ)+1)
    = (8*(n:ℝ))/((4*(n:ℝ)-1)*(4*(n:ℝ)+1)) := by
    field_simp
    ring
  have hD : (4*(n:ℝ))^3 - 4*(n:ℝ) = 4*(n:ℝ)*((4*(n:ℝ)-1)*(4*(n:ℝ)+1)) := by ring
  rw [add_assoc, e, hD]
  have h4P : (4*(n:ℝ)*((4*(n:ℝ)-1)*(4*(n:ℝ)+1))) ≠ 0 := mul_ne_zero h4n h12
  field_simp
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[H_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma H_step (b : ℕ) (x : ℝ) (hx : ((b : ℝ)) = x) (a : ℕ) (ha : a = b + 1) :
  H a = H b + 1/(x+1) := by
  subst ha
  rw [H_succ b, hx]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[partial_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma partial_sum_eq (N : ℕ) :
  ∑ j ∈ Finset.range N, (2:ℝ)/((4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1))
    = H (4*N+1) - 1/2 * H (2*N) - 1 - 1/2 * H N := by
  induction N with
  | zero =>
    have h1 : H 1 = 1 := by
      unfold H
      norm_num [harmonic_succ, harmonic_zero]
    simp only [Finset.sum_range_zero, Nat.mul_zero, Nat.zero_add, H_zero, h1]
    norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hN1 : 1 ≤ N+1 := Nat.le_add_left 1 N
    have te := term_eq (N+1) hN1
    have cast1 : (((N+1 : ℕ)):ℝ) = (N:ℝ)+1 := by push_cast; ring
    rw [cast1] at te
    have r1 : (2*((N:ℝ)+1)) = 2*(N:ℝ)+2 := by ring
    have r2 : (4*((N:ℝ)+1)-1) = 4*(N:ℝ)+3 := by ring
    have r3 : (4*((N:ℝ)+1)+1) = 4*(N:ℝ)+5 := by ring
    have fN : (2:ℝ)/((4*(((N:ℝ))+1))^3 - 4*((((N:ℝ)))+1))
      = -1/(2*(N:ℝ)+2) + 1/(4*(N:ℝ)+3) + 1/(4*(N:ℝ)+5) := by
      have h := te
      rwa [r1, r2, r3] at h
    rw [fN]
    have c41 : (((4*N+1 : ℕ)):ℝ) = 4*(N:ℝ)+1 := by push_cast; ring
    have s1 := H_step (4*N+1) (4*(N:ℝ)+1) c41 (4*N+2) (by ring)
    have c42 : (((4*N+2 : ℕ)):ℝ) = 4*(N:ℝ)+2 := by push_cast; ring
    have s2 := H_step (4*N+2) (4*(N:ℝ)+2) c42 (4*N+3) (by ring)
    have c43 : (((4*N+3 : ℕ)):ℝ) = 4*(N:ℝ)+3 := by push_cast; ring
    have s3 := H_step (4*N+3) (4*(N:ℝ)+3) c43 (4*N+4) (by ring)
    have c44 : (((4*N+4 : ℕ)):ℝ) = 4*(N:ℝ)+4 := by push_cast; ring
    have s4 := H_step (4*N+4) (4*(N:ℝ)+4) c44 (4*N+5) (by ring)
    have e1 : H (4*(N+1)+1) = H (4*N+1) + 1/((4*(N:ℝ))+2) + 1/((4*(N:ℝ))+3)
      + 1/((4*(N:ℝ))+4) + 1/((4*(N:ℝ))+5) := by
      have idx : 4*(N+1)+1 = 4*N+5 := by ring
      rw [idx, s4, s3, s2, s1]
      ring
    have d21 : (((2*N : ℕ)):ℝ) = 2*(N:ℝ) := by push_cast; ring
    have t1 := H_step (2*N) (2*(N:ℝ)) d21 (2*N+1) (by ring)
    have d22 : (((2*N+1 : ℕ)):ℝ) = 2*(N:ℝ)+1 := by push_cast; ring
    have t2 := H_step (2*N+1) (2*(N:ℝ)+1) d22 (2*N+2) (by ring)
    have e2 : H (2*(N+1)) = H (2*N) + 1/((2*(N:ℝ))+1) + 1/((2*(N:ℝ))+2) := by
      have idx : 2*(N+1) = 2*N+2 := by ring
      rw [idx, t2, t1]
      ring
    have e3 : H (N+1) = H N + 1/((N:ℝ)+1) := H_succ N
    rw [e1, e2, e3]
    have key : (-1/(2*(N:ℝ)+2) + 1/(4*(N:ℝ)+3) + 1/(4*(N:ℝ)+5))
      = (1/((4*(N:ℝ))+2) + 1/((4*(N:ℝ))+3) + 1/((4*(N:ℝ))+4) + 1/((4*(N:ℝ))+5))
        - 1/2*(1/((2*(N:ℝ))+1) + 1/((2*(N:ℝ))+2)) - 1/2*(1/((N:ℝ)+1)) := by
      have q1 : (0:ℝ) < 4*(N:ℝ)+2 := by positivity
      have q2 : (0:ℝ) < 4*(N:ℝ)+3 := by positivity
      have q3 : (0:ℝ) < 4*(N:ℝ)+4 := by positivity
      have q4 : (0:ℝ) < 4*(N:ℝ)+5 := by positivity
      have r1n : (0:ℝ) < 2*(N:ℝ)+1 := by positivity
      have r2n : (0:ℝ) < 2*(N:ℝ)+2 := by positivity
      have p1 : (0:ℝ) < (N:ℝ)+1 := by positivity
      have m1 : (4*(N:ℝ)+2) ≠ 0 := ne_of_gt q1
      have m2 : (4*(N:ℝ)+3) ≠ 0 := ne_of_gt q2
      have m3 : (4*(N:ℝ)+4) ≠ 0 := ne_of_gt q3
      have m4 : (4*(N:ℝ)+5) ≠ 0 := ne_of_gt q4
      have k1 : (2*(N:ℝ)+1) ≠ 0 := ne_of_gt r1n
      have k2 : (2*(N:ℝ)+2) ≠ 0 := ne_of_gt r2n
      have n1 : ((N:ℝ)+1) ≠ 0 := ne_of_gt p1
      field_simp
      ring
    linear_combination key

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[D_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma D_pos (m : ℝ) (hm : 1 ≤ m) : (0:ℝ) < (4*m)^3 - 4*m := by
  have h4m : (4:ℝ) ≤ 4*m := by linarith
  have h4mpos : (0:ℝ) < 4*m := by linarith
  have hsq : (1:ℝ) < (4*m)^2 := by nlinarith [hm, h4m, sq_nonneg (4*m - 4)]
  have hfac : (4*m)^3 - 4*m = (4*m)*((4*m)^2 - 1) := by ring
  rw [hfac]
  apply mul_pos h4mpos (by linarith)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[term_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma term_nonneg (j : ℕ) :
  (0:ℝ) ≤ (2:ℝ)/((4*(((j:ℝ))+1))^3 - 4*((((j:ℝ)))+1)) := by
  have hm : (1:ℝ) ≤ (j:ℝ)+1 := by
    have h0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  have hD : (0:ℝ) < (4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1) := D_pos _ hm
  exact div_nonneg (by norm_num) (le_of_lt hD)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[term_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma term_le (j : ℕ) :
  (2:ℝ)/((4*(((j:ℝ))+1))^3 - 4*((((j:ℝ)))+1)) ≤ 1/(((j:ℝ)+1)^2) := by
  have hm : (1:ℝ) ≤ (j:ℝ)+1 := by
    have h0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  have hD : (0:ℝ) < (4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1) := D_pos _ hm
  have hm0 : (0:ℝ) < (j:ℝ)+1 := by linarith
  have hm2 : (0:ℝ) < ((j:ℝ)+1)^2 := pow_pos hm0 2
  have hD2 : (2:ℝ)*(((j:ℝ)+1)^2) ≤ (4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1) := by
    nlinarith [hm, sq_nonneg ((j:ℝ)+1)]
  rw [div_le_iff₀ hD]
  have e : (1/(((j:ℝ)+1)^2)) * ((4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1))
    = ((4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1))/(((j:ℝ)+1)^2) := by ring
  rwa [e, le_div_iff₀ hm2]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[summable_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma summable_comp : Summable (fun j : ℕ => (1:ℝ)/(((j:ℝ)+1)^2)) := by
  have base : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)^(2:ℕ))) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have h := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^(2:ℕ))) 1).mpr base
  simpa using h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[summable_f](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma summable_f :
  Summable (fun j : ℕ => (2:ℝ)/((4*(((j:ℝ))+1))^3 - 4*((((j:ℝ)))+1))) :=
  Summable.of_nonneg_of_le (fun j => term_nonneg j) (fun j => term_le j) summable_comp

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[tendsto_idx4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma tendsto_idx4 : Filter.Tendsto (fun N:ℕ => 4*N+1) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun N => ?_) Filter.tendsto_id
  show N ≤ 4*N+1
  exact Nat.le_trans (Nat.le_mul_of_pos_left N (by norm_num)) (Nat.le_add_right _ _)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[tendsto_idx2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma tendsto_idx2 : Filter.Tendsto (fun N:ℕ => 2*N) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun N => ?_) Filter.tendsto_id
  show N ≤ 2*N
  exact Nat.le_mul_of_pos_left N (by norm_num)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[u1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma u1 : Filter.Tendsto (fun N:ℕ => H (4*N+1) - Real.log (((4*N+1 : ℕ)):ℝ))
  Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  simpa [H, Function.comp_def] using (Real.tendsto_harmonic_sub_log.comp tendsto_idx4)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[u2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma u2 : Filter.Tendsto (fun N:ℕ => H (2*N) - Real.log (((2*N : ℕ)):ℝ))
  Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  simpa [H, Function.comp_def] using (Real.tendsto_harmonic_sub_log.comp tendsto_idx2)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[u3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma u3 : Filter.Tendsto (fun N:ℕ => H N - Real.log ((N:ℝ)))
  Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  simpa [H] using Real.tendsto_harmonic_sub_log

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[h1N](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma h1N : Filter.Tendsto (fun N:ℕ => (1:ℝ)/(N:ℝ)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun N:ℕ => ((N:ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa [one_div] using h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[h4c](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma h4c : Filter.Tendsto (fun _ : ℕ => (4:ℝ)) Filter.atTop (nhds 4) :=
  tendsto_const_nhds

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[h4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma h4 : Filter.Tendsto (fun N:ℕ => (4:ℝ) + 1/(N:ℝ)) Filter.atTop (nhds 4) := by
  have h := h4c.add h1N
  simpa using h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hlog](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hlog : Filter.Tendsto (fun N:ℕ => Real.log (4 + 1/(N:ℝ))) Filter.atTop (nhds (Real.log 4)) :=
  (Real.continuousAt_log (by norm_num : (4:ℝ) ≠ 0)).tendsto.comp h4

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hM](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hM : Filter.Tendsto (fun N:ℕ => Real.log (4 + 1/(N:ℝ)) - 1/2*Real.log 2)
  Filter.atTop (nhds (Real.log 4 - 1/2*Real.log 2)) :=
  hlog.sub_const _

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hlog4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hlog4 : Real.log 4 = 2*Real.log 2 := by
  have h4eq : (4:ℝ) = 2^2 := by norm_num
  rw [h4eq, Real.log_pow]
  norm_num

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hM2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hM2 : Filter.Tendsto (fun N:ℕ => Real.log (4 + 1/(N:ℝ)) - 1/2*Real.log 2)
  Filter.atTop (nhds (3/2*Real.log 2)) := by
  have h := hM
  rw [hlog4] at h
  have e : (2*Real.log 2 - 1/2*Real.log 2) = 3/2*Real.log 2 := by ring
  rwa [e] at h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hML](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hML : (fun N:ℕ => Real.log (4 + 1/(N:ℝ)) - 1/2*Real.log 2) =ᶠ[Filter.atTop]
  (fun N:ℕ => Real.log (((4*N+1 : ℕ)):ℝ) - 1/2*Real.log (((2*N : ℕ)):ℝ) - 1/2*Real.log ((N:ℝ))) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  show Real.log (4 + 1/(N:ℝ)) - 1/2*Real.log 2
    = Real.log (((4*N+1 : ℕ)):ℝ) - 1/2*Real.log (((2*N : ℕ)):ℝ) - 1/2*Real.log ((N:ℝ))
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hn : (0:ℝ) < (N:ℝ) := by linarith
  have hn0 : (N:ℝ) ≠ 0 := ne_of_gt hn
  have h1n : (0:ℝ) < 1/(N:ℝ) := one_div_pos.mpr hn
  have h41 : (4:ℝ)+1/(N:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have e1 : (((4*N+1 : ℕ)):ℝ) = (N:ℝ)*(4+1/(N:ℝ)) := by
    push_cast
    field_simp
  have e2 : (((2*N : ℕ)):ℝ) = 2*(N:ℝ) := by push_cast; ring
  rw [e1, e2, Real.log_mul hn0 h41, Real.log_mul (by norm_num) hn0]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hL](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hL : Filter.Tendsto
  (fun N:ℕ => Real.log (((4*N+1 : ℕ)):ℝ) - 1/2*Real.log (((2*N : ℕ)):ℝ) - 1/2*Real.log ((N:ℝ)))
  Filter.atTop (nhds (3/2*Real.log 2)) :=
  hM2.congr' hML

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[c12](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma c12 : Filter.Tendsto (fun _ : ℕ => (1/2:ℝ)) Filter.atTop (nhds (1/2)) :=
  tendsto_const_nhds

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hAf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hAf : Filter.Tendsto (fun N:ℕ => (H (4*N+1) - Real.log (((4*N+1 : ℕ)):ℝ))
  - 1/2*(H (2*N) - Real.log (((2*N : ℕ)):ℝ)) - 1/2*(H N - Real.log ((N:ℝ))))
  Filter.atTop (nhds (Real.eulerMascheroniConstant - 1/2*Real.eulerMascheroniConstant
    - 1/2*Real.eulerMascheroniConstant)) :=
  (u1.sub (c12.mul u2)).sub (c12.mul u3)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hS_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hS_eq : ∀ N:ℕ, ((H (4*N+1) - Real.log (((4*N+1 : ℕ)):ℝ))
  - 1/2*(H (2*N) - Real.log (((2*N : ℕ)):ℝ)) - 1/2*(H N - Real.log ((N:ℝ)))
  + (Real.log (((4*N+1 : ℕ)):ℝ) - 1/2*Real.log (((2*N : ℕ)):ℝ) - 1/2*Real.log ((N:ℝ))) - 1)
  = (∑ j ∈ Finset.range N, (2:ℝ)/((4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1))) := by
  intro N
  rw [partial_sum_eq]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hcomb](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hcomb : Filter.Tendsto (fun N:ℕ => (H (4*N+1) - Real.log (((4*N+1 : ℕ)):ℝ))
  - 1/2*(H (2*N) - Real.log (((2*N : ℕ)):ℝ)) - 1/2*(H N - Real.log ((N:ℝ)))
  + (Real.log (((4*N+1 : ℕ)):ℝ) - 1/2*Real.log (((2*N : ℕ)):ℝ) - 1/2*Real.log ((N:ℝ))) - 1)
  Filter.atTop (nhds ((Real.eulerMascheroniConstant - 1/2*Real.eulerMascheroniConstant
    - 1/2*Real.eulerMascheroniConstant) + 3/2*Real.log 2 - 1)) :=
  (hAf.add hL).sub_const 1

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hT](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hT : Filter.Tendsto
  (fun N:ℕ => ∑ j ∈ Finset.range N, (2:ℝ)/((4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1)))
  Filter.atTop (nhds ((Real.eulerMascheroniConstant - 1/2*Real.eulerMascheroniConstant
    - 1/2*Real.eulerMascheroniConstant) + 3/2*Real.log 2 - 1)) :=
  hcomb.congr (fun N => hS_eq N)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hval : (Real.eulerMascheroniConstant - 1/2*Real.eulerMascheroniConstant
  - 1/2*Real.eulerMascheroniConstant) + 3/2*Real.log 2 - 1 = 3/2*Real.log 2 - 1 := by
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[hT'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma hT' : Filter.Tendsto
  (fun N:ℕ => ∑ j ∈ Finset.range N, (2:ℝ)/((4*((j:ℝ)+1))^3 - 4*((j:ℝ)+1)))
  Filter.atTop (nhds (3/2*Real.log 2 - 1)) := by
  have h := hT
  rwa [hval] at h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary

/--
[ramanujan_part1_ch2_entry4_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry4_corollary
  :
-- imply
  HasSum (fun j : ℕ => (2 : ℝ) / ((4 * ((j : ℝ) + 1)) ^ 3 - 4 * ((j : ℝ) + 1)))
    ((3 : ℝ) / 2 * Real.log 2 - 1) := by
-- proof
  exact (Summable.hasSum_iff_tendsto_nat summable_f).mpr hT'

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary


-- created on 2026-10-20
-- updated on 2026-10-23
