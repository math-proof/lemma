import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.PolyEquivProb
open PolyEquivProb
open Finset MvPolynomial Fintype


namespace PolyEquivProb

/--
[equiv_agreement_prob_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma equiv_agreement_prob_eq_one
  [CommRing F]
  [IsDomain F]
  [Fintype F]
  [DecidableEq F]
  {m : ℕ}
  {p₁ p₂ : MvPolynomial (Fin m) F}
-- given
  (heq : p₁ = p₂) :
-- imply
  agreementProb p₁ p₂ = 1 := by
-- proof
  subst heq
  unfold agreementProb
  have hfilt : (Finset.univ.filter (fun r : Fin m → F =>
    MvPolynomial.eval r p₁ = MvPolynomial.eval r p₁)) = Finset.univ := by
    ext r; simp
  rw [hfilt, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  push_cast
  exact div_self (by positivity)

end PolyEquivProb

namespace PolyEquivProb

/--
[nonequiv_agreement_prob_le_third](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma nonequiv_agreement_prob_le_third
  [CommRing F]
  [IsDomain F]
  [Fintype F]
  [DecidableEq F]
  {m : ℕ}
  {p₁ p₂ : MvPolynomial (Fin m) F}
-- given
  (hne : p₁ ≠ p₂)
  (hdeg : ∀ i : Fin m, (p₁ - p₂).degreeOf i ≤ 1)
  (hF : 3 * m ≤ Fintype.card F) :
-- imply
  agreementProb p₁ p₂ ≤ 1 / 3 := by
-- proof
  unfold agreementProb
  have hfilt : (Finset.univ.filter (fun r : Fin m → F =>
    MvPolynomial.eval r p₁ = MvPolynomial.eval r p₂)) =
    (Finset.univ.filter (fun r : Fin m → F =>
      MvPolynomial.eval r (p₁ - p₂) = 0)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_sub]
    exact sub_eq_zero.symm
  rw [hfilt, Fintype.piFinset_univ.symm]
  have hsub_ne : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hne
  have sz := MvPolynomial.schwartz_zippel_sum_degreeOf hsub_ne
    (fun _ => (Finset.univ : Finset F))
  simp only [Finset.card_univ] at sz
  have hcF : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) := by
    exact_mod_cast Fintype.card_pos (α := F)
  calc ((Fintype.piFinset fun _ => Finset.univ).filter
    (fun r : Fin m → F => MvPolynomial.eval r (p₁ - p₂) = 0)).card /
    ((Fintype.card F : ℚ≥0) ^ m)
    = ((Fintype.piFinset fun _ => Finset.univ).filter
      (fun r : Fin m → F => MvPolynomial.eval r (p₁ - p₂) = 0)).card /
      (∏ _ : Fin m, (Fintype.card F : ℚ≥0)) := by simp
    _ ≤ ∑ i : Fin m, ((p₁ - p₂).degreeOf i : ℚ≥0) /
      (Fintype.card F : ℚ≥0) := sz
    _ ≤ ∑ _ : Fin m, ((1 : ℚ≥0) / (Fintype.card F : ℚ≥0)) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact Nat.cast_le.mpr (hdeg i)
    _ = (m : ℚ≥0) * 1 / (Fintype.card F : ℚ≥0) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    _ = (m : ℚ≥0) / (Fintype.card F : ℚ≥0) := by ring
    _ ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hcF (by norm_num : (0 : ℚ≥0) < 3)]
      simp only [one_mul]
      calc (m : ℚ≥0) * 3 = ((3 * m : ℕ) : ℚ≥0) := by push_cast; ring
        _ ≤ (Fintype.card F : ℚ≥0) := Nat.cast_le.mpr hF

end PolyEquivProb

namespace PolyEquivProb

/--
[indicator_eval_eq_ite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma indicator_eval_eq_ite
  {m : ℕ}
  [CommRing F]
  {S : Finset (Fin m)}
  {v : Fin m → Bool} :
-- imply
  (∏ i ∈ S, (if v i = true then (1 : F) else 0)) * (∏ i ∈ Finset.univ \ S, ((1 : F) - if v i = true then 1 else 0)) = if S = boolSupport v then 1 else 0 := by
-- proof
  split_ifs with hS
  · subst hS
    have h1 : ∏ i ∈ boolSupport v, (if v i = true then (1 : F) else 0) = 1 := by
      apply Finset.prod_eq_one; intro i hi
      rw [boolSupport, Finset.mem_filter] at hi; simp [hi.2]
    have h2 : ∏ i ∈ Finset.univ \ boolSupport v, ((1 : F) - if v i = true then 1 else 0) = 1 := by
      apply Finset.prod_eq_one; intro i hi
      rw [Finset.mem_sdiff] at hi; have := hi.2
      rw [boolSupport, Finset.mem_filter] at this; push Not at this
      simp [Bool.eq_false_iff.mpr (this (Finset.mem_univ _))]
    rw [h1, h2, one_mul]
  · by_cases h1 : ∃ i ∈ S, v i ≠ true
    · obtain ⟨i, hiS, hvi⟩ := h1
      exact mul_eq_zero_of_left (Finset.prod_eq_zero hiS (by simp [Bool.eq_false_iff.mpr hvi])) _
    · push Not at h1
      have hS_sub : S ⊆ boolSupport v := fun i hi => by
        rw [boolSupport, Finset.mem_filter]; exact ⟨Finset.mem_univ i, h1 i hi⟩
      obtain ⟨i, hi_bS, hi_nS⟩ := Finset.exists_of_ssubset
        (Finset.ssubset_iff_subset_ne.mpr ⟨hS_sub, hS⟩)
      have hvi : v i = true := by rw [boolSupport, Finset.mem_filter] at hi_bS; exact hi_bS.2
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi_nS⟩) (by simp [hvi]))

end PolyEquivProb

namespace PolyEquivProb

/--
[boolVec_boolSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma boolVec_boolSupport
  {m : ℕ}
  {v : Fin m → Bool} :
-- imply
  (fun i => decide (i ∈ boolSupport v)) = v := by
-- proof
  ext i
  simp only [boolSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases v i <;> simp

end PolyEquivProb

namespace PolyEquivProb

/--
[eval_multilinearExtension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma eval_multilinearExtension
  {m : ℕ}
  [CommRing F]
  {f : (Fin m → Bool) → F}
  {v : Fin m → Bool} :
-- imply
  MvPolynomial.eval (boolToField v) (multilinearExtension f) = f v := by
-- proof
  unfold multilinearExtension
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_sub, map_one,
    MvPolynomial.eval_X, boolToField]
  conv_lhs =>
    arg 2; ext S
    rw [mul_assoc]
  simp_rw [indicator_eval_eq_ite]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [boolVec_boolSupport]

end PolyEquivProb

namespace PolyEquivProb

/--
[degreeOf_indicator_term_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma degreeOf_indicator_term_le
  {m : ℕ}
  [CommRing F]
  [IsDomain F]
  {S : Finset (Fin m)}
  {n : Fin m}
  {c : F} :
-- imply
  degreeOf n (MvPolynomial.C c * (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin m) F)) * (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - MvPolynomial.X i))) ≤ 1 := by
-- proof
  have hprodS : degreeOf n (∏ i ∈ S, (X i : MvPolynomial (Fin m) F)) ≤
    if n ∈ S then 1 else 0 := by
    calc degreeOf n (∏ i ∈ S, (X i : MvPolynomial (Fin m) F))
      ≤ ∑ i ∈ S, degreeOf n (X i : MvPolynomial (Fin m) F) := degreeOf_prod_le _ _ _
      _ = ∑ i ∈ S, (if n = i then 1 else 0) := by
        congr 1; ext i; exact degreeOf_X n i
      _ = if n ∈ S then 1 else 0 := by simp
  have hprodC : degreeOf n (∏ i ∈ Finset.univ \ S,
    ((1 : MvPolynomial (Fin m) F) - X i)) ≤
    if n ∈ Finset.univ \ S then 1 else 0 := by
    calc degreeOf n (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - X i))
      ≤ ∑ i ∈ Finset.univ \ S, degreeOf n ((1 : MvPolynomial (Fin m) F) - X i) :=
        degreeOf_prod_le _ _ _
      _ ≤ ∑ i ∈ Finset.univ \ S, (if n = i then 1 else 0) := by
        gcongr with i _
        calc degreeOf n ((1 : MvPolynomial (Fin m) F) - X i)
          ≤ max (degreeOf n (1 : MvPolynomial (Fin m) F))
            (degreeOf n (X i : MvPolynomial (Fin m) F)) :=
            degreeOf_sub_le _ _ _
          _ = max 0 (if n = i then 1 else 0) := by rw [degreeOf_one, degreeOf_X]
          _ = if n = i then 1 else 0 := by split_ifs <;> simp
      _ = if n ∈ Finset.univ \ S then 1 else 0 := by simp
  calc degreeOf n (C c * (∏ i ∈ S, (X i : MvPolynomial (Fin m) F)) *
    (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - X i)))
    ≤ degreeOf n (C c * ∏ i ∈ S, (X i : MvPolynomial (Fin m) F)) +
      degreeOf n (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - X i)) :=
      degreeOf_mul_le n _ _
    _ ≤ degreeOf n (∏ i ∈ S, (X i : MvPolynomial (Fin m) F)) +
      degreeOf n (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - X i)) := by
      gcongr; exact degreeOf_C_mul_le _ _ _
    _ ≤ (if n ∈ S then 1 else 0) + (if n ∈ Finset.univ \ S then 1 else 0) := by
      gcongr
    _ ≤ 1 := by
      by_cases hn : n ∈ S <;> simp_all [Finset.mem_sdiff]

end PolyEquivProb

namespace PolyEquivProb

/--
[multilinearExtension_degreeOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma multilinearExtension_degreeOf_le
  {m : ℕ}
  [CommRing F]
  [IsDomain F]
  {f : (Fin m → Bool) → F}
  {n : Fin m} :
-- imply
  (multilinearExtension f).degreeOf n ≤ 1 := by
-- proof
  unfold multilinearExtension
  calc degreeOf n (∑ S ∈ Finset.univ.powerset, _)
    ≤ (Finset.univ.powerset).sup (fun S => degreeOf n
      (C (f fun i => decide (i ∈ S)) *
      (∏ i ∈ S, (X i : MvPolynomial (Fin m) F)) *
      (∏ i ∈ Finset.univ \ S, ((1 : MvPolynomial (Fin m) F) - X i)))) :=
      degreeOf_sum_le _ _ _
    _ ≤ 1 := Finset.sup_le (fun S _ => degreeOf_indicator_term_le S n _)

end PolyEquivProb

namespace PolyEquivProb

/--
[arithmetize_eq_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma arithmetize_eq_of_equiv
  {m : ℕ}
  [CommRing F]
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
-- given
  (h : BranchingPrograms.BPEquiv bp₁ bp₂) :
-- imply
  arithmetize (F := F) bp₁ = arithmetize bp₂ := by
-- proof
  unfold arithmetize
  congr 1
  funext v
  rw [h v]

end PolyEquivProb

namespace PolyEquivProb

/--
[equiv_of_arithmetize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma equiv_of_arithmetize_eq
  {m : ℕ}
  [CommRing F]
  [IsDomain F]
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
-- given
  (h : arithmetize (F := F) bp₁ = arithmetize bp₂) :
-- imply
  BranchingPrograms.BPEquiv bp₁ bp₂ := by
-- proof
  intro v
  have h1 := eval_multilinearExtension (F := F) (fun w => if bp₁.eval w then (1 : F) else 0) v
  have h2 := eval_multilinearExtension (F := F) (fun w => if bp₂.eval w then (1 : F) else 0) v
  have heq : MvPolynomial.eval (boolToField v) (arithmetize (F := F) bp₁) =
    MvPolynomial.eval (boolToField v) (arithmetize (F := F) bp₂) := by
    rw [h]
  simp only [arithmetize] at heq
  rw [h1, h2] at heq
  by_cases hb₁ : bp₁.eval v = true
  · simp [hb₁] at heq ⊢
    by_contra hb₂
    simp [Bool.eq_false_iff.mpr hb₂] at heq
  · have hf₁ : bp₁.eval v = false := Bool.eq_false_iff.mpr (by exact hb₁)
    simp [hf₁] at heq ⊢
    by_contra hb₂
    have : bp₂.eval v = true := by
      cases bp₂.eval v <;> simp_all
    simp [this] at heq

end PolyEquivProb

namespace PolyEquivProb

/--
[arithmetize_ne_of_not_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma arithmetize_ne_of_not_equiv
  {m : ℕ}
  [CommRing F]
  [IsDomain F]
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
-- given
  (h : ¬BranchingPrograms.BPEquiv bp₁ bp₂) :
-- imply
  arithmetize (F := F) bp₁ ≠ arithmetize bp₂ :=
-- proof
  fun heq => h (equiv_of_arithmetize_eq bp₁ bp₂ heq)

end PolyEquivProb

namespace PolyEquivProb

/--
[arithmetize_degreeOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma arithmetize_degreeOf_le
  {m : ℕ}
  [CommRing F]
  [IsDomain F]
  {bp : BranchingPrograms.BranchingProgram m}
  {n : Fin m} :
-- imply
  (arithmetize (F := F) bp).degreeOf n ≤ 1 :=
-- proof
  multilinearExtension_degreeOf_le _ n

end PolyEquivProb

namespace PolyEquivProb

/--
[arithmetize_diff_degreeOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma arithmetize_diff_degreeOf_le
  {m : ℕ}
  [CommRing F]
  [IsDomain F]
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
  {n : Fin m} :
-- imply
  (arithmetize (F := F) bp₁ - arithmetize bp₂).degreeOf n ≤ 1 := by
-- proof
  calc (arithmetize (F := F) bp₁ - arithmetize bp₂).degreeOf n
    ≤ max ((arithmetize (F := F) bp₁).degreeOf n) ((arithmetize (F := F) bp₂).degreeOf n) :=
      MvPolynomial.degreeOf_sub_le _ _ _
    _ ≤ max 1 1 := max_le_max (arithmetize_degreeOf_le bp₁ n) (arithmetize_degreeOf_le bp₂ n)
    _ = 1 := by simp

end PolyEquivProb

namespace PolyEquivProb

/--
[equiv_robp_agreement_prob_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma equiv_robp_agreement_prob_eq_one
  [CommRing F]
  [IsDomain F]
  [Fintype F]
  [DecidableEq F]
  {m : ℕ}
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
-- given
  (hequiv : BranchingPrograms.BPEquiv bp₁ bp₂) :
-- imply
  agreementProb (arithmetize (F := F) bp₁) (arithmetize bp₂) = 1 :=
-- proof
  equiv_agreement_prob_eq_one _ _ (arithmetize_eq_of_equiv bp₁ bp₂ hequiv)

end PolyEquivProb

namespace PolyEquivProb

/--
[nonequiv_robp_agreement_prob_le_third](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma nonequiv_robp_agreement_prob_le_third
  [CommRing F]
  [IsDomain F]
  [Fintype F]
  [DecidableEq F]
  {m : ℕ}
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
-- given
  (hne : ¬BranchingPrograms.BPEquiv bp₁ bp₂)
  (hF : 3 * m ≤ Fintype.card F) :
-- imply
  agreementProb (arithmetize (F := F) bp₁) (arithmetize bp₂) ≤ 1 / 3 :=
-- proof
  nonequiv_agreement_prob_le_third _ _
    (arithmetize_ne_of_not_equiv bp₁ bp₂ hne)
    (arithmetize_diff_degreeOf_le bp₁ bp₂)
    hF

end PolyEquivProb

namespace PolyEquivProb

/--
[robp_agreement_claim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyEquivProb.lean)
-/
@[path]
lemma robp_agreement_claim
  [CommRing F]
  [IsDomain F]
  [Fintype F]
  [DecidableEq F]
  {m : ℕ}
  {bp₁ bp₂ : BranchingPrograms.BranchingProgram m}
-- given
  (hF : 3 * m ≤ Fintype.card F) :
-- imply
  (BranchingPrograms.BPEquiv bp₁ bp₂ → agreementProb (arithmetize (F := F) bp₁) (arithmetize bp₂) = 1) ∧ (¬BranchingPrograms.BPEquiv bp₁ bp₂ → agreementProb (arithmetize (F := F) bp₁) (arithmetize bp₂) ≤ 1 / 3) :=
-- proof
  ⟨fun hequiv => equiv_robp_agreement_prob_eq_one bp₁ bp₂ hequiv,
    fun hne => nonequiv_robp_agreement_prob_le_third bp₁ bp₂ hne hF⟩

end PolyEquivProb


-- created on 2026-10-23
