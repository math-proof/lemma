import Mathlib
import sympy.Basic


/--
[image_mul_two_Iio_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Order/Group/Pointwise/Interval.lean)
-/
@[path]
lemma Nat.image_mul_two_Iio_even {n : ℕ} (h : Even n) :
  (2 * ·) '' Set.Iio (n / 2) = { n | Even n } ∩ Set.Iio n := by
  aesop (add simp [even_iff_two_dvd, dvd_iff_exists_eq_mul_right])

/--
[image_mul_two_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Order/Group/Pointwise/Interval.lean)
-/
@[path]
lemma Nat.image_mul_two_Iio (n : ℕ) :
  (2 * ·) '' Set.Iio ((n + 1) / 2) = { n | Even n } ∩ Set.Iio n := by
  aesop (add simp [even_iff_two_dvd, dvd_iff_exists_eq_mul_right, mul_comm, lt_div_iff_mul_lt])

/--
[Nat.image_mul_two_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Order/Group/Pointwise/Interval.lean)
-/
@[path]
private lemma main
  {n : ℕ} :
-- imply
  (fun a => 2 * a) '' Set.Iio ((n + 1) / 2) = { m | Even m } ∩ Set.Iio n := by
-- proof
  ext m
  simp only [Set.mem_image, Set.mem_Iio, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  ·
    rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, by omega⟩, by omega⟩
  ·
    rintro ⟨he, hn⟩
    obtain ⟨a, ha⟩ := he
    subst ha
    exact ⟨a, by omega, by omega⟩


@[path]
private lemma image_mul_two_Iio_even
  {n : ℕ}
-- given
  (h : Even n) :
-- imply
  (fun a => 2 * a) '' Set.Iio (n / 2) = { m | Even m } ∩ Set.Iio n := by
-- proof
  ext m
  simp only [Set.mem_image, Set.mem_Iio, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  ·
    rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, by omega⟩, by omega⟩
  ·
    rintro ⟨he, hn⟩
    obtain ⟨a, ha⟩ := he
    subst ha
    obtain ⟨k, hk⟩ := h
    subst hk
    exact ⟨a, by omega, by omega⟩


-- created on 2026-10-09
-- updated on 2026-10-23
