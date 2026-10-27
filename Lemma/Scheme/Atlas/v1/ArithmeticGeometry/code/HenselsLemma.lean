import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.ArithmeticGeometry.code.HenselsLemma
open Polynomial PadicInt
open PadicInt


/--
[double_root_iff_derivative_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HenselsLemma.lean)
-/
@[path]
lemma double_root_iff_derivative_root
  [CommRing R]
  {f : R[X]}
  {a : R} :
-- imply
  (f.eval a = 0 ∧ (derivative f).eval a = 0) ↔ (X - C a) ^ 2 ∣ f := by
-- proof
  constructor
  ·
    rintro ⟨hf, hf'⟩
    have h1 : (X - C a) ∣ f := dvd_iff_isRoot.mpr hf
    obtain ⟨q, hq⟩ := h1
    have hq_eval : q.eval a = 0 := by
      have key : (derivative f).eval a = q.eval a := by
        rw [hq, derivative_mul, eval_add, eval_mul, eval_mul,
          derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
          one_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
      rwa [hf'] at key
    have h2 : (X - C a) ∣ q := dvd_iff_isRoot.mpr hq_eval
    obtain ⟨r, hr⟩ := h2
    exact ⟨r, by rw [hq, hr]; ring⟩
  ·
    rintro ⟨g, hg⟩
    constructor
    ·
      rw [hg, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    ·
      rw [hg, derivative_mul, derivative_pow]
      simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
        zero_pow (by norm_num : (2 : ℕ) - 1 ≠ 0), derivative_sub, derivative_X, derivative_C,
        sub_zero]
      ring
open PadicInt

/--
[PadicInt.norm_eq_one_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HenselsLemma.lean)
-/
@[path]
lemma PadicInt.norm_eq_one_of_not_dvd
  {p : ℕ}
  [Fact p.Prime]
  {x : ℤ_[p]}
-- given
  (h : ¬ (↑p ∣ x)) :
-- imply
  ‖x‖ = 1 := by
-- proof
  rw [← PadicInt.isUnit_iff]
  by_contra h'
  exact h ((PadicInt.norm_lt_one_iff_dvd x).mp (PadicInt.not_isUnit_iff.mp h'))

/--
[hensel_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HenselsLemma.lean)
-/
@[path]
lemma hensel_lemma
  {p : ℕ}
  [Fact p.Prime]
  {f : Polynomial ℤ_[p]}
  {a : ℤ_[p]}
-- given
  (hfa : (↑p : ℤ_[p]) ∣ Polynomial.aeval a f)
  (hda : ¬ (↑p : ℤ_[p]) ∣ Polynomial.aeval a (Polynomial.derivative f)) :
-- imply
  ∃! b : ℤ_[p], Polynomial.aeval b f = 0 ∧ (↑p : ℤ_[p]) ∣ (b - a) := by
-- proof
  have hfa_norm : ‖Polynomial.aeval a f‖ < 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mpr hfa
  have hda_norm : ‖Polynomial.aeval a (Polynomial.derivative f)‖ = 1 :=
    PadicInt.norm_eq_one_of_not_dvd _ hda
  have hnorm : ‖Polynomial.aeval a f‖ <
    ‖Polynomial.aeval a (Polynomial.derivative f)‖ ^ 2 := by
    rw [hda_norm]; norm_num; exact hfa_norm
  obtain ⟨z, hz_root, hz_dist, _, hz_unique⟩ := hensels_lemma hnorm
  refine ⟨z, ⟨hz_root, ?_⟩, ?_⟩
  ·
    exact (PadicInt.norm_lt_one_iff_dvd _).mp (by rw [hda_norm] at hz_dist; exact hz_dist)
  ·
    intro y ⟨hy_root, hy_dvd⟩
    have hy_norm : ‖y - a‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr hy_dvd
    exact hz_unique y hy_root (by rw [hda_norm]; exact hy_norm)

/--
[hensel_lemma_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HenselsLemma.lean)
-/
@[path]
lemma hensel_lemma_norm
  {p : ℕ}
  [Fact p.Prime]
  {f : Polynomial ℤ_[p]}
  {a : ℤ_[p]}
-- given
  (hfa : ‖Polynomial.aeval a f‖ < 1)
  (hda : ‖Polynomial.aeval a (Polynomial.derivative f)‖ = 1) :
-- imply
  ∃! b : ℤ_[p], Polynomial.aeval b f = 0 ∧ ‖b - a‖ < 1 := by
-- proof
  have hnorm : ‖Polynomial.aeval a f‖ <
    ‖Polynomial.aeval a (Polynomial.derivative f)‖ ^ 2 := by
    rw [hda]; norm_num; exact hfa
  obtain ⟨z, hz_root, hz_dist, _, hz_unique⟩ := hensels_lemma hnorm
  refine ⟨z, ⟨hz_root, by rw [hda] at hz_dist; exact hz_dist⟩, ?_⟩
  intro y ⟨hy_root, hy_close⟩
  exact hz_unique y hy_root (by rw [hda]; exact hy_close)


-- created on 2026-10-23
