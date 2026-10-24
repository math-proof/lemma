import Mathlib
import sympy.Basic
open Polynomial


/--
[Polynomial.eval_and_derivative_eval_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor913.lean)
-/
@[path]
lemma Polynomial.eval_and_derivative_eval_eq_zero_iff
  [CommRing R]
  {f : R[X]}
  {a : R} :
-- imply
  f.eval a = 0 ∧ f.derivative.eval a = 0 ↔ ∃ g : R[X], f = (X - C a) ^ 2 * g := by
-- proof
  constructor
  ·
    rintro ⟨hf, hf'⟩
    have h0 : (taylor a f).coeff 0 = 0 := by rw [taylor_coeff_zero, hf]
    have h1 : (taylor a f).coeff 1 = 0 := by rw [taylor_coeff_one, hf']
    have hdvd : X ^ 2 ∣ taylor a f := by
      rw [X_pow_dvd_iff]
      intro d hd
      obtain _ | _ | _ <;> simp_all := d
    obtain ⟨g, hg⟩ := hdvd
    refine ⟨taylor (-a) g, ?_⟩
    have key : f = taylor (-a) (taylor a f) := by
      rw [taylor_taylor, neg_add_cancel, taylor_zero]
    rw [key, hg, taylor_mul, taylor_pow, taylor_X, map_neg, sub_eq_add_neg]
  ·
    rintro ⟨g, hg⟩
    refine ⟨?_, ?_⟩
    · rw [hg, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    · rw [hg, derivative_mul, derivative_pow, eval_add, eval_mul, eval_mul]
      simp [eval_sub, eval_X, eval_C, sub_self]


-- created on 2026-10-23
