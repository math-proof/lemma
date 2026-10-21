import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Real.RpowMulSum_AddSub.le.Prod_Pow.of.All_Any_Eq_RothRidoutExponent.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Real


private lemma roth_ridout_prime_product_eq_h
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (k : RothMvIndex m) :
  (∏ l ∈ S, p l ^ rothRidoutExponent r a b k l) =
    ∏ h, (∏ l ∈ S, p l ^ a h l) ^ k h *
      (∏ l ∈ S, p l ^ b h l) ^ (r h - k h) := by
  classical
  unfold rothRidoutExponent
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [pow_add, pow_mul]
  simp only [Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  congr 1
  rw [Finset.prod_comm]

private lemma roth_ridout_prime_product_dvd_monomial_h
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (q : Fin m → ℚ)
-- given
  (hnum : ∀ h, ((∏ l ∈ S, p l ^ a h l : ℕ) : ℤ) ∣ (q h).num)
  (hden : ∀ h, (∏ l ∈ S, p l ^ b h l) ∣ (q h).den)
  (k : RothMvIndex m) :
-- imply
  ((∏ l ∈ S, p l ^ rothRidoutExponent r a b k l : ℕ) : ℤ) ∣
    ∏ h, (q h).num ^ k h * ((q h).den : ℤ) ^ (r h - k h) := by
-- proof
  rw [roth_ridout_prime_product_eq_h]
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

private lemma roth_ridout_exists_common_divisor_h
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
  refine (Int.natCast_dvd_natCast.mpr ?_).trans
    (roth_ridout_prime_product_dvd_monomial_h S p r a b q hnum hden k) |>.mul_left _
  apply Finset.prod_dvd_prod_of_dvd
  intro l hl
  exact pow_dvd_pow (p l) (hle l hl k hk)

/--
[roth_ridout_exists_hasse_clear_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (S : Finset ι)
  (p : ι → ℕ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (μ ν : ι → ℝ)
  (c : RothCoeff r)
  (Q T θ : ℝ)
  (i : RothMvIndex m)
-- given
  (hr : ∀ h, 0 < r h)
  (hQ : 1 < Q)
  (hθ : 0 ≤ θ)
  (hμ : ∀ l ∈ S, 0 ≤ μ l)
  (hν : ∀ l ∈ S, 0 ≤ ν l)
  (hpower : ∀ h, Q ≤ ((q h).den : ℝ) ^ r h)
  (hnum : ∀ h, ((∏ l ∈ S, p l ^ a h l : ℕ) : ℤ) ∣ (q h).num)
  (hden : ∀ h, (∏ l ∈ S, p l ^ b h l) ∣ (q h).den)
  (ha : ∀ h l, l ∈ S →
    Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ a h l)
  (hb : ∀ h l, l ∈ S →
    Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ b h l)
  (hbalanced : ∀ j, c j ≠ 0 →
    T ≤ rothWeight r (fun h ↦ j h) ∧
      rothWeight r (fun h ↦ j h) ≤ (m : ℝ) - T)
  (hi : rothMvWeight r i ≤ θ) :
-- imply
  ∃ G : ℕ,
    Real.rpow Q ((∑ l ∈ S, (μ l + ν l)) * (T - θ)) ≤ G ∧
    (G : ℤ) ∣ rothClearEval (rothMvHasse i (rothMvOfCoeff c)) q r := by
-- proof
  let Pi := rothMvHasse i (rothMvOfCoeff c)
  if hsupp : Pi.support.Nonempty then
    obtain ⟨e, hmin, _, hdvd⟩ :=
      roth_ridout_exists_common_divisor_h S p Pi q r a b hsupp hnum hden
    let G := ∏ l ∈ S, p l ^ e l
    refine ⟨G, ?_, ?_⟩
    ·
      exact RpowMulSum_AddSub.le.Prod_Pow.of.All_Any_Eq_RothRidoutExponent.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
        S p q r a b μ ν c Q T θ i e
        hr hQ hθ hμ hν hpower ha hb hbalanced hi hmin
    ·
      exact hdvd
  else
    let G := ⌈Real.rpow Q ((∑ l ∈ S, (μ l + ν l)) * (T - θ))⌉₊
    refine ⟨G, Nat.le_ceil _, ?_⟩
    have hsupport : Pi.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsupp
    rw [show rothClearEval Pi q r = 0 by simp [rothClearEval, hsupport]]
    exact dvd_zero _


-- created on 2026-10-21
