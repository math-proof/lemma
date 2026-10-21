import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_ridout_exists_common_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
-- given
  (hsupp : P.support.Nonempty)
  (hnum : ∀ h, ((∏ l ∈ S, p l ^ a h l : ℕ) : ℤ) ∣ (q h).num)
  (hden : ∀ h, (∏ l ∈ S, p l ^ b h l) ∣ (q h).den) :
-- imply
  ∃ e : ι → ℕ,
    (∀ l ∈ S, ∃ k ∈ P.support, e l = rothRidoutExponent r a b k l) ∧
    (∀ l ∈ S, ∀ k ∈ P.support, e l ≤ rothRidoutExponent r a b k l) ∧
    ((∏ l ∈ S, p l ^ e l : ℕ) : ℤ) ∣ rothClearEval P q r := by
-- proof
  classical
  have prime_product_eq (k : RothMvIndex m) :
    (∏ l ∈ S, p l ^ rothRidoutExponent r a b k l) =
      ∏ h, (∏ l ∈ S, p l ^ a h l) ^ k h *
        (∏ l ∈ S, p l ^ b h l) ^ (r h - k h) := by
    unfold rothRidoutExponent
    simp_rw [← Finset.prod_pow_eq_pow_sum]
    simp_rw [pow_add, pow_mul]
    simp only [Finset.prod_mul_distrib]
    simp_rw [← Finset.prod_pow]
    rw [Finset.prod_comm]
    congr 1
    rw [Finset.prod_comm]
  have prime_product_dvd_monomial (k : RothMvIndex m) :
    ((∏ l ∈ S, p l ^ rothRidoutExponent r a b k l : ℕ) : ℤ) ∣
      ∏ h, (q h).num ^ k h * ((q h).den : ℤ) ^ (r h - k h) := by
    rw [prime_product_eq]
    push_cast
    apply Finset.prod_dvd_prod_of_dvd
    intro h _
    apply mul_dvd_mul
    ·
      have hnumh := hnum h
      push_cast at hnumh
      exact pow_dvd_pow_of_dvd hnumh _
    ·
      apply pow_dvd_pow_of_dvd
      have hdenh := hden h
      exact_mod_cast hdenh
  let e : ι → ℕ := fun l ↦
    P.support.inf' hsupp fun k ↦ rothRidoutExponent r a b k l
  have hmin : ∀ l ∈ S, ∃ k ∈ P.support,
      e l = rothRidoutExponent r a b k l := by
    intro l _
    obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image P.support
      (fun j ↦ rothRidoutExponent r a b j l) hsupp
    refine ⟨k, hk, le_antisymm ?_ ?_⟩
    ·
      dsimp [e]
      exact Finset.inf'_le _ hk
    ·
      dsimp [e]
      exact Finset.le_inf' hsupp _ fun j hj ↦ hkmin j hj
  have hle : ∀ l ∈ S, ∀ k ∈ P.support,
      e l ≤ rothRidoutExponent r a b k l := by
    intro l _ k hk
    dsimp [e]
    exact Finset.inf'_le _ hk
  refine ⟨e, hmin, hle, ?_⟩
  unfold rothClearEval
  apply Finset.dvd_sum
  intro k hk
  have hsmallNat :
    (∏ l ∈ S, p l ^ e l) ∣
      ∏ l ∈ S, p l ^ rothRidoutExponent r a b k l := by
    apply Finset.prod_dvd_prod_of_dvd
    intro l hl
    exact pow_dvd_pow (p l) (hle l hl k hk)
  apply dvd_trans _ ((prime_product_dvd_monomial k).mul_left _)
  exact_mod_cast hsmallNat


-- created on 2026-10-21
