/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/PosOfAscentProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.LengthDecreaseNeg
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DihedralPositivity
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DihedralPositivityFinite
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ParabolicPositivity

set_option maxHeartbeats 800000

open CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Pointwise linearity of $\sigma_w$ on vectors supported in $\{s, t\}$:
$\sigma_w(v)(u) = v_s \cdot \sigma_w(\alpha_s)(u) + v_t \cdot \sigma_w(\alpha_t)(u)$. -/
theorem wordSigma_of_supported_two (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B) (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    wordSigma M word v = fun u =>
      v s * wordSigma M word (e s) u + v t * wordSigma M word (e t) u := by
  have hv : v = v s • e s + v t • e t := by
    ext u
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_apply]
    by_cases hus : u = s
    · subst hus; simp [hst]
    · by_cases hut : u = t
      · subst hut; simp [Ne.symm hst]
      · simp [hus, hut, hsupp u hus hut]
  conv_lhs => rw [hv]
  rw [wordSigma_add]
  simp only [wordSigma_smul]
  ext u; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- Inductive step (Case B) of the positivity-on-ascent argument: handles the case where
$t$ ascends $w$ on the right but $s$ descends $w$. The argument reduces to a smaller
word via parabolic decomposition. -/
theorem pos_of_ascent_case_b {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (n : ℕ)
    (ih : ∀ m < n, ∀ (word : List B) (s : B),
      word.length = m → cs.IsReduced word →
      cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word) →
      IsPositive (wordSigma M word (e s)))
    (init : List B) (s t : B)
    (hts : t ≠ s)
    (hred_init : cs.IsReduced init)
    (hasc_t : cs.length (cs.wordProd init * cs.simple t) > cs.length (cs.wordProd init))
    (hdesc_s : cs.length (cs.wordProd init * cs.simple s) < cs.length (cs.wordProd init))
    (hasc : cs.length (cs.wordProd (init ++ [t]) * cs.simple s) >
            cs.length (cs.wordProd (init ++ [t])))
    (hinit_len : init.length < n) :
    IsPositive (wordSigma M (init ++ [t]) (e s)) := by
  sorry

/-- Strong-induction proof of positivity on ascent: if $w$ is reduced and $s$ ascends
$w$ on the right, then $\sigma_w(\alpha_s)$ is a positive vector. -/
theorem pos_of_ascent_proof {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) :
    ∀ (n : ℕ) (word : List B) (s : B),
    word.length = n →
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) > cs.length (cs.wordProd word) →
    IsPositive (wordSigma M word (e s)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro word s hlen hred hasc

  rcases word.eq_nil_or_concat' with rfl | ⟨init, t, rfl⟩
  ·
    intro u; simp [wordSigma, e, Pi.single_apply]; split <;> linarith
  ·

    have hts : t ≠ s := by
      intro heq; subst heq
      have h1 : cs.length (cs.wordProd (init ++ [t]) * cs.simple t) ≤ init.length := by
        rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
            mul_assoc, cs.simple_mul_simple_self, mul_one]
        exact cs.length_wordProd_le init
      have h2 : cs.length (cs.wordProd (init ++ [t])) = (init ++ [t]).length := hred
      simp at h2; omega

    have hred_init : cs.IsReduced init := by
      unfold CoxeterSystem.IsReduced at hred ⊢
      have hle := cs.length_wordProd_le init
      rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one] at hred
      simp at hred
      rcases cs.length_mul_simple (cs.wordProd init) t with h1 | h1 <;> omega
    have hasc_t : cs.length (cs.wordProd init * cs.simple t) >
                  cs.length (cs.wordProd init) := by
      have hred_i : cs.length (cs.wordProd init) = init.length := hred_init
      have hred_full := hred; unfold CoxeterSystem.IsReduced at hred_full
      rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one] at hred_full
      simp at hred_full; omega
    have hinit_len : init.length < n := by simp at hlen; omega

    have ih_t : IsPositive (wordSigma M init (e t)) :=
      ih init.length hinit_len init t rfl hred_init (by omega)

    rcases cs.length_mul_simple (cs.wordProd init) s with hasc_s | hdesc_s
    ·
      have ih_s : IsPositive (wordSigma M init (e s)) :=
        ih init.length hinit_len init s rfl hred_init (by omega)


      have hfv : formVal M s t ≤ 0 := formVal_nonpos_of_ne M s t (Ne.symm hts)
      have hst : s ≠ t := Ne.symm hts
      have hdecomp : wordSigma M (init ++ [t]) (e s) = wordSigma M init (sigma M t (e s)) := by
        rw [wordSigma_append, wordSigma_singleton]
      have hsupp : ∀ u, u ≠ s → u ≠ t → (sigma M t (e s)) u = 0 :=
        sigma_support_two M s t hst t (Or.inr rfl) (e s) (e_supported_two s t)
      have hcoeff_s : (sigma M t (e s)) s = 1 := by
        rw [sigma_coord_ne M t (e s) s hts.symm]; simp [e]
      have hcoeff_t : (sigma M t (e s)) t = -2 * formVal M s t := by
        rw [sigma_t_coord_t_of_supported M s t hst (e s) (e_supported_two s t)]
        simp [e, hst]
      have hlin := wordSigma_of_supported_two M s t hst init (sigma M t (e s)) hsupp
      rw [hdecomp]
      intro u
      have := congr_fun hlin u
      rw [this, hcoeff_s, hcoeff_t]
      have h1 := ih_s u
      have h2 := ih_t u
      nlinarith

    ·
      exact pos_of_ascent_case_b M cs n ih init s t hts hred_init (by omega) (by omega) hasc hinit_len

/-- Positivity on ascent: for a reduced word $w$ with $\ell(ws) > \ell(w)$, the vector
$\sigma_w(\alpha_s)$ is positive. -/
theorem pos_of_ascent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hasc : cs.length (cs.wordProd word * cs.simple s) >
            cs.length (cs.wordProd word)) :
    IsPositive (wordSigma M word (e s)) :=
  pos_of_ascent_proof M cs word.length word s rfl hred hasc

/-- Negativity on descent: for a reduced word $w$ with $\ell(ws) < \ell(w)$, the vector
$\sigma_w(\alpha_s)$ is negative. -/
theorem neg_of_descent {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W)
    (word : List B) (s : B)
    (hred : cs.IsReduced word)
    (hdesc : cs.length (cs.wordProd word * cs.simple s) <
             cs.length (cs.wordProd word)) :
    IsNegative (wordSigma M word (e s)) := by

  set w := cs.wordProd word
  obtain ⟨word', hred', hprod'⟩ := cs.exists_reduced_word (w * cs.simple s)


  have hasc' : cs.length (cs.wordProd word' * cs.simple s) >
               cs.length (cs.wordProd word') := by
    rw [← hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]
    exact hdesc

  have hpos := pos_of_ascent M cs word' s hred' hasc'

  have hprod_eq : cs.wordProd (word' ++ [s]) = w := by
    rw [cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
        ← hprod', mul_assoc, cs.simple_mul_simple_self, mul_one]

  have hflip := wordSigma_append_s_neg M word' s

  have hinv := wordSigma_eq_of_wordProd_eq M cs (word' ++ [s]) word hprod_eq (e s)

  intro t
  have : wordSigma M word (e s) t = -(wordSigma M word' (e s) t) := by
    rw [← hinv]; exact congr_fun hflip t
  rw [this]
  linarith [hpos t]

end CoxeterGroup
