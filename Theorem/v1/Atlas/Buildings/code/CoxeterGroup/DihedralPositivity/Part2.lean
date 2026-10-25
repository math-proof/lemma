/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralPositivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Roots
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part4
import Def.v1.Atlas.Buildings.code.CoxeterGroup.DihedralPositivity
open Finset BigOperators


namespace CoxeterGroup

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Every letter of $\mathtt{altWordEven}\,s\,t\,n$ is either $s$ or $t$. -/
theorem altWordEven_mem (s t : B) (n : ℕ) :
    ∀ b ∈ altWordEven s t n, b = s ∨ b = t := by
  induction n with
  | zero => simp [altWordEven]
  | succ k ih =>
    intro b hb
    simp [altWordEven] at hb
    rcases hb with rfl | rfl | hb
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact ih b hb

/-- $\mathtt{altWordEven}\,s\,t\,n$ has length exactly $2n$. -/
theorem altWordEven_length (s t : B) (n : ℕ) :
    (altWordEven s t n).length = 2 * n := by
  induction n with
  | zero => simp [altWordEven]
  | succ k ih => simp [altWordEven, ih]; ring

/-- Affine (infinite-order) closed forms for the dihedral iterate of $e_s$
along an even-length alternating word: the $s$-coordinate is $1 + 2n$ and
the $t$-coordinate is $2n$, reflecting the unipotent action when
$m(s, t) = \infty$. -/
theorem dihedral_coords_even_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    wordSigma M (altWordEven s t n) (e s) s = 1 + 2 * (n : ℝ) ∧
    wordSigma M (altWordEven s t n) (e s) t = 2 * (n : ℝ) := by
  have hfv : formVal M s t = -1 := formVal_eq_neg_one_of_zero M s t hm
  have hfvts : formVal M t s = -1 := by rw [formVal_symm]; exact hfv
  induction n with
  | zero =>
    simp [altWordEven, e, hst]
  | succ k ih =>
    simp only [altWordEven, wordSigma]
    set v := wordSigma M (altWordEven s t k) (e s)
    have hvs : v s = 1 + 2 * (k : ℝ) := ih.1
    have hvt : v t = 2 * (k : ℝ) := ih.2
    have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
      wordSigma_support_two M s t hst (altWordEven s t k)
        (altWordEven_mem s t k) (e s) (e_supported_two s t)

    set w := sigma M t v
    have hws : w s = v s := sigma_coord_ne M t v s hst
    have hwt : w t = -v t - 2 * v s * formVal M s t :=
      sigma_t_coord_t_of_supported M s t hst v hv_supp
    have hw_supp : ∀ u, u ≠ s → u ≠ t → w u = 0 :=
      sigma_support_two M s t hst t (Or.inr rfl) v hv_supp

    have hrs : sigma M s w s = -w s - 2 * w t * formVal M t s :=
      sigma_s_coord_s_of_supported M s t hst w hw_supp
    have hrt : sigma M s w t = w t := sigma_coord_ne M s w t (Ne.symm hst)
    constructor
    ·
      rw [hrs, hws, hwt, hvs, hvt, hfv, hfvts]
      push_cast; ring
    ·
      rw [hrt, hwt, hvs, hvt, hfv]
      push_cast; ring

/-- Odd-length analogue for $m(s, t) = \infty$: the $s$-coordinate stays
$1 + 2n$ while the $t$-coordinate becomes $2n + 2$. -/
theorem dihedral_coords_odd_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    wordSigma M (t :: altWordEven s t n) (e s) s = 1 + 2 * (n : ℝ) ∧
    wordSigma M (t :: altWordEven s t n) (e s) t = 2 * (n : ℝ) + 2 := by
  have hfv : formVal M s t = -1 := formVal_eq_neg_one_of_zero M s t hm
  simp only [wordSigma]
  set v := wordSigma M (altWordEven s t n) (e s)
  have ⟨hvs, hvt⟩ := dihedral_coords_even_infinite M s t hst hm n
  have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
    wordSigma_support_two M s t hst (altWordEven s t n)
      (altWordEven_mem s t n) (e s) (e_supported_two s t)
  constructor
  ·
    have : sigma M t v s = v s := sigma_coord_ne M t v s hst
    rw [this]; exact hvs
  ·
    have : sigma M t v t = -v t - 2 * v s * formVal M s t :=
      sigma_t_coord_t_of_supported M s t hst v hv_supp
    rw [this, show v s = 1 + 2 * (n : ℝ) from hvs, show v t = 2 * (n : ℝ) from hvt, hfv]
    ring

/-- In the infinite-order case $m(s, t) = 0$, the even-length alternating
iterate of $e_s$ is unconditionally positive. -/
theorem dihedral_pos_even_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    IsPositive (wordSigma M (altWordEven s t n) (e s)) := by
  have ⟨hvs, hvt⟩ := dihedral_coords_even_infinite M s t hst hm n
  intro u
  by_cases hus : u = s
  · rw [hus, hvs]; positivity
  · by_cases hut : u = t
    · rw [hut, hvt]; positivity
    · rw [wordSigma_support_two M s t hst (altWordEven s t n)
        (altWordEven_mem s t n) (e s) (e_supported_two s t) u hus hut]

/-- Odd-length analogue: in the infinite-order case the iterate
$\mathtt{wordSigma}\,M\,(t :: \text{altWord})\,(e_s)$ is also unconditionally
positive. -/
theorem dihedral_pos_odd_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    IsPositive (wordSigma M (t :: altWordEven s t n) (e s)) := by
  have ⟨hvs, hvt⟩ := dihedral_coords_odd_infinite M s t hst hm n
  intro u
  by_cases hus : u = s
  · rw [hus, hvs]; positivity
  · by_cases hut : u = t
    · rw [hut, hvt]; positivity
    · have hmem : ∀ b ∈ t :: altWordEven s t n, b = s ∨ b = t := by
        intro b hb
        simp at hb
        rcases hb with rfl | hb
        · exact Or.inr rfl
        · exact altWordEven_mem s t n b hb
      rw [wordSigma_support_two M s t hst (t :: altWordEven s t n)
        hmem (e s) (e_supported_two s t) u hus hut]

end CoxeterGroup
