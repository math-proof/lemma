import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DihedralPositivity
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

/--
[sigma_t_pos_of_t_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_t_pos_of_t_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hpos : IsPositive v)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
  (hvt : v t = 0) :
-- imply
  IsPositive (sigma M t v) := by
-- proof
  intro u
  if hut : u = t then
    rw [hut, sigma_coord_self]
    suffices h : bilinForm M v (e t) ≤ 0 by linarith [hvt]
    simp only [bilinForm, e, Pi.single_apply]
    simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    apply Finset.sum_nonpos
    intro r _
    if hrt : r = t then
      simp [hrt, hvt]
    else if hrs : r = s then
      rw [hrs]
      exact mul_nonpos_of_nonneg_of_nonpos (hpos s) (formVal_nonpos_of_ne M s t hst)
    else
      rw [hsupp r hrs hrt, zero_mul]
  else if hus : u = s then
    rw [hus, sigma_coord_ne M t v s hst]
    exact hpos s
  else
    rw [sigma_support_two M s t hst t (Or.inr rfl) v hsupp u hus hut]

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_s_pos_of_s_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_s_pos_of_s_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hpos : IsPositive v)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
  (hvs : v s = 0) :
-- imply
  IsPositive (sigma M s v) := by
-- proof
  intro u
  if hus : u = s then
    rw [hus, sigma_coord_self]
    suffices h : bilinForm M v (e s) ≤ 0 by linarith [hvs]
    simp only [bilinForm, e, Pi.single_apply]
    simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    apply Finset.sum_nonpos
    intro r _
    if hrs : r = s then
      simp [hrs, hvs]
    else if hrt : r = t then
      rw [hrt]
      exact mul_nonpos_of_nonneg_of_nonpos (hpos t)
        (formVal_nonpos_of_ne M t s (Ne.symm hst))
    else
      rw [hsupp r hrs hrt, zero_mul]
  else if hut : u = t then
    rw [hut, sigma_coord_ne M s v t (Ne.symm hst)]
    exact hpos t
  else
    rw [sigma_support_two M s t hst s (Or.inl rfl) v hsupp u hus hut]

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_t_pos_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_t_pos_general
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hpos : IsPositive v)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
  (hineq : v t ≤ -2 * v s * formVal M s t) :
-- imply
  IsPositive (sigma M t v) := by
-- proof
  intro u
  if hut : u = t then
    rw [hut, sigma_t_coord_t_of_supported M s t hst v hsupp]
    linarith
  else if hus : u = s then
    rw [hus, sigma_coord_ne M t v s hst]
    exact hpos s
  else
    rw [sigma_support_two M s t hst t (Or.inr rfl) v hsupp u hus hut]

end CoxeterGroup

namespace CoxeterGroup

/--
[sigma_s_pos_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_s_pos_general
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hpos : IsPositive v)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
  (hineq : v s ≤ -2 * v t * formVal M t s) :
-- imply
  IsPositive (sigma M s v) := by
-- proof
  intro u
  if hus : u = s then
    rw [hus, sigma_s_coord_s_of_supported M s t hst v hsupp]
    linarith
  else if hut : u = t then
    rw [hut, sigma_coord_ne M s v t (Ne.symm hst)]
    exact hpos t
  else
    rw [sigma_support_two M s t hst s (Or.inl rfl) v hsupp u hus hut]

end CoxeterGroup

namespace CoxeterGroup

/--
[formVal_le_neg_sqrt2_div2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma formVal_le_neg_sqrt2_div2
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (_ : s ≠ t)
  (hm : M s t = 0 ∨ M s t ≥ 4) :
-- imply
  formVal M s t ≤ -(Real.sqrt 2 / 2) := by
-- proof
  obtain hm0 | hm4 := hm
  ·
    rw [formVal_eq_neg_one_of_zero M s t hm0]
    have : Real.sqrt 2 / 2 ≤ 1 := by
      have h2 : Real.sqrt 2 ≤ 2 := by
        have := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
        nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 2)]
      linarith
    linarith
  ·
    unfold formVal
    split
    ·
      omega
    ·
      rename_i hm0
      have hm_ge_4 : (4 : ℝ) ≤ (M s t : ℝ) := by exact_mod_cast hm4
      have hm_pos : (0 : ℝ) < (M s t : ℝ) := by linarith
      have hle : Real.pi / (M s t : ℝ) ≤ Real.pi / 4 := by
        apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity) hm_ge_4
      have hge : (0 : ℝ) ≤ Real.pi / (M s t : ℝ) := by positivity
      have hpi : Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
      have hcos : Real.cos (Real.pi / (M s t : ℝ)) ≥ Real.sqrt 2 / 2 := by
        rw [ge_iff_le, ← Real.cos_pi_div_four]
        exact Real.cos_le_cos_of_nonneg_of_le_pi hge hpi hle
      linarith

end CoxeterGroup

/--
[sigma_support_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_support_two_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t r : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hr : r = s ∨ r = t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  ∀ u, u ≠ s → u ≠ t → sigma M r v u = 0 := by
-- proof
  apply CoxeterGroup.sigma_support_two M s t hst r hr v hsupp

/--
[wordSigma_support_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma wordSigma_support_two_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {word : List B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (halt : ∀ b ∈ word, b = s ∨ b = t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  ∀ u, u ≠ s → u ≠ t → wordSigma M word v u = 0 := by
-- proof
  apply CoxeterGroup.wordSigma_support_two M s t hst word halt v hsupp

/--
[e_supported_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma e_supported_two_eq
  [DecidableEq B]
  [Fintype B]
  {s t : B} :
-- imply
  ∀ u, u ≠ s → u ≠ t → (e s) u = 0 := by
-- proof
  apply CoxeterGroup.e_supported_two s t

/--
[formVal_le_neg_half](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma formVal_le_neg_half_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M s t ≠ 2) :
-- imply
  formVal M s t ≤ -1/2 := by
-- proof
  apply CoxeterGroup.formVal_le_neg_half M s t hst hm

/--
[dihedral_pos_len2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma dihedral_pos_len2_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hst : s ≠ t)
  (hm : M s t ≠ 2) :
-- imply
  IsPositive (wordSigma M [s, t] (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_len2 M s t hst hm

/--
[bilinForm_e_t_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma bilinForm_e_t_of_supported_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  bilinForm M v (e t) = v s * formVal M s t + v t := by
-- proof
  apply CoxeterGroup.bilinForm_e_t_of_supported M s t hst v hsupp

/--
[bilinForm_e_s_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma bilinForm_e_s_of_supported_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  bilinForm M v (e s) = v s + v t * formVal M t s := by
-- proof
  apply CoxeterGroup.bilinForm_e_s_of_supported M s t hst v hsupp

/--
[sigma_t_coord_t_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_t_coord_t_of_supported_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  sigma M t v t = -v t - 2 * v s * formVal M s t := by
-- proof
  apply CoxeterGroup.sigma_t_coord_t_of_supported M s t hst v hsupp

/--
[sigma_s_coord_s_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma sigma_s_coord_s_of_supported_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  sigma M s v s = -v s - 2 * v t * formVal M t s := by
-- proof
  apply CoxeterGroup.sigma_s_coord_s_of_supported M s t hst v hsupp

/--
[formVal_eq_neg_one_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma formVal_eq_neg_one_of_zero_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
-- given
  (hm : M s t = 0) :
-- imply
  formVal M s t = -1 := by
-- proof
  apply CoxeterGroup.formVal_eq_neg_one_of_zero M s t hm

/--
[altWordEven_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma altWordEven_mem_eq
  [DecidableEq B]
  [Fintype B]
  {s t : B}
  {n : ℕ} :
-- imply
  ∀ b ∈ altWordEven s t n, b = s ∨ b = t := by
-- proof
  apply CoxeterGroup.altWordEven_mem s t n

/--
[altWordEven_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma altWordEven_length_eq
  [DecidableEq B]
  [Fintype B]
  {s t : B}
  {n : ℕ} :
-- imply
  (altWordEven s t n).length = 2 * n := by
-- proof
  apply CoxeterGroup.altWordEven_length s t n

/--
[dihedral_coords_even_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma dihedral_coords_even_infinite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t = 0) :
-- imply
  wordSigma M (altWordEven s t n) (e s) s = 1 + 2 * (n : ℝ) ∧ wordSigma M (altWordEven s t n) (e s) t = 2 * (n : ℝ) := by
-- proof
  apply CoxeterGroup.dihedral_coords_even_infinite M s t hst hm n

/--
[dihedral_coords_odd_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma dihedral_coords_odd_infinite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t = 0) :
-- imply
  wordSigma M (t :: altWordEven s t n) (e s) s = 1 + 2 * (n : ℝ) ∧ wordSigma M (t :: altWordEven s t n) (e s) t = 2 * (n : ℝ) + 2 := by
-- proof
  apply CoxeterGroup.dihedral_coords_odd_infinite M s t hst hm n

/--
[dihedral_pos_even_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma dihedral_pos_even_infinite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t = 0) :
-- imply
  IsPositive (wordSigma M (altWordEven s t n) (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_even_infinite M s t hst hm n

/--
[dihedral_pos_odd_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean)
-/
@[path]
private lemma dihedral_pos_odd_infinite_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {n : ℕ}
-- given
  (hst : s ≠ t)
  (hm : M s t = 0) :
-- imply
  IsPositive (wordSigma M (t :: altWordEven s t n) (e s)) := by
-- proof
  apply CoxeterGroup.dihedral_pos_odd_infinite M s t hst hm n


-- created on 2026-10-23
-- updated on 2026-10-24
