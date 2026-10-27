import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.Cyclotomic.LehmerLaurentIdentity.Part3
open MetaMathlibExt


namespace MetaMathlibExt

/--
[zeta_isPrimitiveRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
  IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 :=
  Complex.exp_ne_zero _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_pow_two_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_pow_two_ne_one (n : ℕ) (hn : 2 < n) : (zeta n) ^ 2 ≠ 1 := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  intro h
  have hdvd : n ∣ 2 := (IsPrimitiveRoot.pow_eq_one_iff_dvd hζ 2).mp h
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_norm (n : ℕ) : ‖zeta n‖ = 1 := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
    = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold zeta
  rw [harg, Complex.norm_exp_ofReal_mul_I]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_conj (n : ℕ) :
  (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ := by
  have h1 : zeta n * (starRingEnd ℂ) (zeta n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, zeta_norm n]
    norm_num
  have h3 := congrArg (· ⁻¹) (eq_inv_of_mul_eq_one_left h1)
  simpa using h3.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_not_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_not_real (n : ℕ) (hn : 2 < n) :
  (starRingEnd ℂ) (zeta n) ≠ zeta n := by
  intro h
  have hc := zeta_conj n
  rw [h] at hc
  have h2 : (zeta n) ^ 2 = 1 := by
    calc (zeta n) ^ 2 = zeta n * zeta n := by ring
    _ = zeta n * (zeta n)⁻¹ := by rw [← hc]
    _ = 1 := mul_inv_cancel₀ (zeta_ne_zero n)
  exact zeta_pow_two_ne_one n hn h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[trace_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma trace_conj (n : ℕ) :
  (starRingEnd ℂ) (zeta n + (zeta n)⁻¹) = zeta n + (zeta n)⁻¹ := by
  have hc := zeta_conj n
  have hci : (starRingEnd ℂ) ((zeta n)⁻¹) = zeta n := by
    rw [map_inv₀, hc, inv_inv]
  rw [map_add, hc, hci, add_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[conj_fix_adjoin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma conj_fix_adjoin (n : ℕ) (z : ℂ)
  (hz : z ∈ IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) :
  (starRingEnd ℂ) z = z := by
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact trace_conj n
  · intro x
    exact Complex.conj_ofReal x
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
  · intro x _ hx
    rw [map_inv₀, hx]
  · intro x y _ _ hx hy
    rw [map_mul, hx, hy]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_not_mem_adjoin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_not_mem_adjoin (n : ℕ) (hn : 2 < n) :
  zeta n ∉ IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ) := by
  intro hmem
  exact zeta_not_real n hn (conj_fix_adjoin n _ hmem)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_inv_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_inv_eq_pow (n : ℕ) (hn : 0 < n) :
  (zeta n)⁻¹ = (zeta n) ^ (n - 1) := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have h1 : zeta n * (zeta n) ^ (n - 1) = 1 := by
    have hnp : 1 + (n - 1) = n := by omega
    calc zeta n * (zeta n) ^ (n - 1)
      = (zeta n) ^ (1 + (n - 1)) := by rw [pow_add, pow_one]
      _ = (zeta n) ^ n := by rw [hnp]
      _ = 1 := hζ.pow_eq_one
  have h2 := congrArg (· ⁻¹) (eq_inv_of_mul_eq_one_left h1)
  simpa using h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_isIntegral (n : ℕ) (hn : 0 < n) : IsIntegral ℤ (zeta n) := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  refine ⟨Polynomial.X ^ n - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
  simp [hζ.pow_eq_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_inv_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_inv_isIntegral (n : ℕ) (hn : 0 < n) :
  IsIntegral ℤ ((zeta n)⁻¹) := by
  rw [zeta_inv_eq_pow n hn]
  exact (zeta_isIntegral n hn).pow _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[trace_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma trace_isIntegral (n : ℕ) (hn : 0 < n) :
  IsIntegral ℤ (zeta n + (zeta n)⁻¹) :=
  (zeta_isIntegral n hn).add (zeta_inv_isIntegral n hn)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[psi_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma psi_monic (n : ℕ) (hn : 0 < n) :
  (minpoly ℤ (zeta n + (zeta n)⁻¹)).Monic :=
  minpoly.monic (trace_isIntegral n hn)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[natDegree_psi_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma natDegree_psi_rat (n : ℕ) (hn : 0 < n) :
  (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree
    = (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree := by
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions
    (R := ℤ) (S := ℂ) (K := ℚ) (L := ℂ) (trace_isIntegral n hn)
  simp only [Algebra.algebraMap_self_apply] at hmap
  rw [hmap, (psi_monic n hn).natDegree_map]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[zeta_quad](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma zeta_quad (n : ℕ) :
  (zeta n) ^ 2 = (zeta n + (zeta n)⁻¹) * zeta n - 1 := by
  have h0 := zeta_ne_zero n
  field_simp
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[quadPoly_rest_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma quadPoly_rest_degree (n : ℕ) :
  (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
    IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ *
    Polynomial.X) + 1 :
    Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))).degree
    < 2 := by
  compute_degree
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[quadPoly_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma quadPoly_monic (n : ℕ) : (quadPoly n).Monic :=
  Polynomial.monic_X_pow_add (quadPoly_rest_degree n)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[quadPoly_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma quadPoly_natDegree (n : ℕ) : (quadPoly n).natDegree = 2 := by
  have hlt : (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
    IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ *
    Polynomial.X) + 1 :
    Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))).degree
    < (Polynomial.X ^ 2 : Polynomial
      (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))).degree := by
    rw [Polynomial.degree_X_pow]
    exact quadPoly_rest_degree n
  have hdeg : (quadPoly n).degree = 2 := by
    have h := Polynomial.degree_add_eq_left_of_degree_lt hlt
    rwa [Polynomial.degree_X_pow] at h
  have hnat := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  exact hnat

end MetaMathlibExt

namespace MetaMathlibExt

/--
[quadPoly_aeval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma quadPoly_aeval (n : ℕ) :
  Polynomial.aeval (zeta n) (quadPoly n) = 0 := by
  have hq := zeta_quad n
  have hcoe : algebraMap ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) ℂ
    ⟨zeta n + (zeta n)⁻¹, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
    = zeta n + (zeta n)⁻¹ := rfl
  unfold quadPoly
  simp only [map_add, map_neg, map_mul, map_pow, map_one, Polynomial.aeval_X,
    Polynomial.aeval_C, hcoe]
  linear_combination hq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[minpoly_K1_natDegree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma minpoly_K1_natDegree_eq_two (n : ℕ) (hn : 2 < n) :
  (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
    (zeta n)).natDegree = 2 := by
  have hQ : IsIntegral ℚ (zeta n) := (zeta_isIntegral n (by omega)).tower_top
  have hint : IsIntegral ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
    (zeta n) :=
    hQ.tower_top
  have hupper : (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
    (zeta n)).natDegree ≤ 2 := by
    have hdvd : minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n) ∣ quadPoly n :=
      minpoly.dvd _ _ (quadPoly_aeval n)
    calc (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n)).natDegree
      ≤ (quadPoly n).natDegree :=
        (minpoly.monic hint).natDegree_le_of_dvd (quadPoly_monic n).ne_zero hdvd
      _ = 2 := quadPoly_natDegree n
  have hlower : 2 ≤ (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
    (zeta n)).natDegree := by
    have hpos := minpoly.natDegree_pos hint
    by_contra hlt
    have h1 : (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n)).natDegree = 1 := by omega
    rw [minpoly.natDegree_eq_one_iff] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' : (c : ℂ) = zeta n := hc
    have hmem := c.property
    rw [hc'] at hmem
    exact zeta_not_mem_adjoin n hn hmem
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mem_affine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma mem_affine (n : ℕ) (w : ℂ)
  (hw : w ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :
  ∃ a b : ↥(baseField n),
    algebraMap ↥(baseField n) ℂ a + algebraMap ↥(baseField n) ℂ b * zeta n = w := by
  have hmem_s : zeta n + (zeta n)⁻¹ ∈ baseField n :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hw
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  · intro q
    exact ⟨algebraMap ℚ ↥(baseField n) q, 0, by simp⟩
  · intro x y _ _ ihx ihy
    obtain ⟨a₁, b₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, h₂⟩ := ihy
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    simp only [map_add]
    linear_combination h₁ + h₂
  · intro x _ ihx
    obtain ⟨a, b, h⟩ := ihx
    by_cases hu : algebraMap ↥(baseField n) ℂ a
      + algebraMap ↥(baseField n) ℂ b * zeta n = 0
    · refine ⟨0, 0, ?_⟩
      rw [← h, hu, inv_zero]
      simp
    · have hca : (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a)
      = algebraMap ↥(baseField n) ℂ a :=
      conj_fix_adjoin n _ a.property
      have hcb : (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ b)
        = algebraMap ↥(baseField n) ℂ b :=
        conj_fix_adjoin n _ b.property
      have hcu : (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a
        + algebraMap ↥(baseField n) ℂ b * zeta n)
        = algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹ := by
        rw [map_add, map_mul, hca, hcb, zeta_conj n]
      have hN0 : (algebraMap ↥(baseField n) ℂ a
        + algebraMap ↥(baseField n) ℂ b * zeta n)
        * (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * zeta n) ≠ 0 :=
        mul_ne_zero hu (by
          intro h0
          apply hu
          have h1 := congrArg (starRingEnd ℂ) h0
          simpa using h1)
      have hzz : zeta n * (zeta n)⁻¹ = 1 := mul_inv_cancel₀ (zeta_ne_zero n)
      have hs' : algebraMap ↥(baseField n) ℂ ⟨zeta n + (zeta n)⁻¹, hmem_s⟩
        = zeta n + (zeta n)⁻¹ := rfl
      have hNval : (algebraMap ↥(baseField n) ℂ a
        + algebraMap ↥(baseField n) ℂ b * zeta n)
        * (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * zeta n)
        = algebraMap ↥(baseField n) ℂ
          (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
        rw [hcu]
        simp only [map_add, map_mul, map_pow, hs']
        linear_combination (algebraMap ↥(baseField n) ℂ b ^ 2) * hzz
      have hN'0 : a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2 ≠ 0 := by
        intro hz
        apply hN0
        rw [hNval, hz, map_zero]
      refine ⟨(a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
        / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2),
        (-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2), ?_⟩
      rw [← h]
      have hinv : (zeta n)⁻¹ = (zeta n + (zeta n)⁻¹) - zeta n := by ring
      have hNv0 : algebraMap ↥(baseField n) ℂ
        (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) ≠ 0 := by
        intro hz
        apply hN'0
        exact Subtype.val_injective
          (show ((a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2 :
            ↥(baseField n)) : ℂ) = ((0 : ↥(baseField n)) : ℂ) from hz)
      have hCeq : (algebraMap ↥(baseField n) ℂ
        ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
          / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
        + algebraMap ↥(baseField n) ℂ
          ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
          * zeta n)
        = (algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹)
        / algebraMap ↥(baseField n) ℂ
          (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
        simp only [map_div₀, map_add, map_mul, map_neg, map_pow]
        rw [div_mul_eq_mul_div, ← add_div]
        congr 1
        linear_combination (algebraMap ↥(baseField n) ℂ b) * hs'
          - (algebraMap ↥(baseField n) ℂ b) * hinv
      have hCN : (algebraMap ↥(baseField n) ℂ
        ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
          / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
        + algebraMap ↥(baseField n) ℂ
          ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
          * zeta n)
        * algebraMap ↥(baseField n) ℂ
          (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
        = (algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹) := by
        rw [hCeq]
        exact div_mul_cancel₀ _ hNv0
      have key : (algebraMap ↥(baseField n) ℂ a
        + algebraMap ↥(baseField n) ℂ b * zeta n)
        * (algebraMap ↥(baseField n) ℂ
          ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
            / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
        + algebraMap ↥(baseField n) ℂ
          ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
          * zeta n) = 1 := by
        have h1 : ((algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * zeta n)
          * (algebraMap ↥(baseField n) ℂ
            ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
              / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
          + algebraMap ↥(baseField n) ℂ
            ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
            * zeta n))
          * algebraMap ↥(baseField n) ℂ
            (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
          = algebraMap ↥(baseField n) ℂ
            (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
          calc ((algebraMap ↥(baseField n) ℂ a
            + algebraMap ↥(baseField n) ℂ b * zeta n)
            * (algebraMap ↥(baseField n) ℂ
              ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
            + algebraMap ↥(baseField n) ℂ
              ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              * zeta n))
            * algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
            = (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * zeta n)
              * ((algebraMap ↥(baseField n) ℂ
                ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                  / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              + algebraMap ↥(baseField n) ℂ
                ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                * zeta n)
              * algebraMap ↥(baseField n) ℂ
                (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)) := by
              ring
            _ = (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * zeta n)
              * (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹) := by
              rw [hCN]
            _ = algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
              rwa [← hcu]
        have h2 : ((algebraMap ↥(baseField n) ℂ a
          + algebraMap ↥(baseField n) ℂ b * zeta n)
          * (algebraMap ↥(baseField n) ℂ
            ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
              / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
          + algebraMap ↥(baseField n) ℂ
            ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
            * zeta n))
          * algebraMap ↥(baseField n) ℂ
            (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
          = 1 * algebraMap ↥(baseField n) ℂ
            (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
          rw [h1, one_mul]
        exact mul_right_cancel₀ hNv0 h2
      exact eq_inv_of_mul_eq_one_right key
  · intro x y _ _ ihx ihy
    obtain ⟨a₁, b₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, h₂⟩ := ihy
    refine ⟨a₁ * a₂ - b₁ * b₂,
      a₁ * b₂ + a₂ * b₁ + b₁ * b₂ * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩, ?_⟩
    have hq := zeta_quad n
    have hs' : algebraMap ↥(baseField n) ℂ ⟨zeta n + (zeta n)⁻¹, hmem_s⟩
      = zeta n + (zeta n)⁻¹ := rfl
    rw [← h₁, ← h₂]
    simp only [map_add, map_sub, map_mul, hs']
    linear_combination (-(algebraMap ↥(baseField n) ℂ b₁
      * algebraMap ↥(baseField n) ℂ b₂)) * hq

end MetaMathlibExt

namespace MetaMathlibExt

/--
[finrank_adjoin_zeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma finrank_adjoin_zeta (n : ℕ) (hn : 0 < n) :
  Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) = n.totient := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have hInt : IsIntegral ℚ (zeta n) := (zeta_isIntegral n hn).tower_top
  rw [IntermediateField.adjoin.finrank hInt,
    ← Polynomial.cyclotomic_eq_minpoly_rat hζ hn,
    Polynomial.natDegree_cyclotomic]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[finrank_adjoin_trace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma finrank_adjoin_trace (n : ℕ) (hn : 0 < n) :
  Module.finrank ℚ ↥(baseField n)
    = (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree :=
  IntermediateField.adjoin.finrank ((trace_isIntegral n hn).tower_top)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeE_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma coeE_add (n : ℕ) (u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) :
  ((u + v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
  = (u : ℂ) + (v : ℂ) := by
simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeE_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma coeE_mul (n : ℕ) (u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) :
  ((u * v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
  = (u : ℂ) * (v : ℂ) := by
simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeE_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma coeE_one (n : ℕ) :
  ((1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ) = 1 := by
simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeE_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma coeE_zero (n : ℕ) :
  ((0 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ) = 0 := by
simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coeE_zeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma coeE_zeta (n : ℕ) (hmemE : zeta n ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :
  (((⟨zeta n, hmemE⟩ : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) : ℂ)
  = zeta n :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[clearPoly_aeval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma clearPoly_aeval (n : ℕ) :
  Polynomial.aeval (zeta n) (clearPoly n) = 0 := by
  have hψ0 : Polynomial.aeval (zeta n + (zeta n)⁻¹)
    (minpoly ℤ (zeta n + (zeta n)⁻¹)) = 0 :=
    minpoly.aeval ℤ _
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range (e + 1),
    Polynomial.aeval (zeta n)
      (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
        * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1) ^ k))
    = (zeta n) ^ e * (algebraMap ℤ ℂ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (zeta n + (zeta n)⁻¹) ^ k) := by
    intro k hk
    have hke : k ≤ e := by
      have hmem := Finset.mem_range.mp hk
      omega
    simp only [map_mul, map_pow, map_add, map_one, Polynomial.aeval_C,
      Polynomial.aeval_X]
    have hZ : (zeta n) ^ 2 + 1 = zeta n * (zeta n + (zeta n)⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ (zeta_ne_zero n)]
      ring
    have hpow : (zeta n) ^ (e - k) * (zeta n) ^ k = (zeta n) ^ e := by
      rw [← pow_add, Nat.sub_add_cancel hke]
    rw [hZ, mul_pow]
    linear_combination (algebraMap ℤ ℂ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (zeta n + (zeta n)⁻¹) ^ k) * hpow
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum2 : (∑ k ∈ Finset.range (e + 1),
    (algebraMap ℤ ℂ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (zeta n + (zeta n)⁻¹) ^ k))
    = Polynomial.aeval (zeta n + (zeta n)⁻¹)
      (minpoly ℤ (zeta n + (zeta n)⁻¹)) := by
    have h := Polynomial.as_sum_range_C_mul_X_pow (minpoly ℤ (zeta n + (zeta n)⁻¹))
    have h2 := congrArg (Polynomial.aeval (zeta n + (zeta n)⁻¹)) h
    simp only [map_sum, Polynomial.aeval_C, map_mul, map_pow,
      Polynomial.aeval_X] at h2
    rw [← he] at h2
    rw [← h2]
  rw [hsum2, hψ0, mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[clearPoly_term_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma clearPoly_term_natDegree (n : ℕ) (k : ℕ)
  (hke : k ≤ (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree) :
  (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
    * (Polynomial.X ^ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree - k)
      * (Polynomial.X ^ 2 + 1) ^ k)).natDegree
  ≤ (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree + k := by
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hX2 : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by
    compute_degree
    exact one_ne_zero
  have hC : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)).natDegree
    ≤ 0 :=
    le_of_eq (Polynomial.natDegree_C _)
  have hX : (Polynomial.X ^ (e - k) : Polynomial ℤ).natDegree = e - k :=
    Polynomial.natDegree_X_pow (e - k)
  have hQ : ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree = k * 2 := by
    rw [Polynomial.natDegree_pow, hX2]
  have hmul : (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree
    ≤ (Polynomial.X ^ (e - k) : Polynomial ℤ).natDegree
      + ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree :=
    Polynomial.natDegree_mul_le
  have hmul2 : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
    * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k)).natDegree
    ≤ (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)).natDegree
      + (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree :=
    Polynomial.natDegree_mul_le
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[clearPoly_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma clearPoly_natDegree_le (n : ℕ) :
  (clearPoly n).natDegree ≤ 2 * (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree := by
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have key : ∀ t : Finset ℕ, t ⊆ Finset.range (e + 1) →
    (∑ k ∈ t, Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1) ^ k)).natDegree
    ≤ 2 * e := by
    intro t
    induction t using Finset.induction with
    | empty =>
      intro _
      simp
    | @insert a s has ih =>
      intro hsub
      rw [Finset.sum_insert has]
      refine le_trans (Polynomial.natDegree_add_le _ _) (Nat.max_le.mpr ⟨?_, ?_⟩)
      · have hamem : a ∈ Finset.range (e + 1) := hsub (Finset.mem_insert_self a s)
        have hale : a ≤ e := by
          have hmem := Finset.mem_range.mp hamem
          omega
        have hle : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff a)
          * (Polynomial.X ^ (e - a) * (Polynomial.X ^ 2 + 1) ^ a)).natDegree
          ≤ e + a :=
          clearPoly_term_natDegree n a (by omega)
        omega
      · exact ih ((Finset.subset_insert a s).trans hsub)
  exact key _ (Finset.Subset.rfl)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[clearPoly_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma clearPoly_coeff (n : ℕ) (hn : 2 < n) :
  (clearPoly n).coeff (2 * (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree) = 1 := by
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hae : (minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff e = 1 :=
    (psi_monic n (by omega)).coeff_natDegree
  have hXe : (Polynomial.X ^ (e - e) : Polynomial ℤ) = 1 := by
    rw [Nat.sub_self, pow_zero]
  have hX2monic : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).Monic := by
    apply Polynomial.monic_X_pow_add
    rw [Polynomial.degree_one]
    decide
  have hX2deg : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by
    compute_degree
    exact one_ne_zero
  have hmain : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff e)
    * (Polynomial.X ^ (e - e) * (Polynomial.X ^ 2 + 1) ^ e)).coeff (2 * e)
    = 1 := by
    have hterm : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff e)
      * (Polynomial.X ^ (e - e) * (Polynomial.X ^ 2 + 1) ^ e))
      = (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ e := by
      simp only [hae, hXe, Polynomial.C_1, one_mul]
    rw [hterm]
    have hmonic : ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ e).Monic :=
      hX2monic.pow e
    have hdeg : ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ e).natDegree = 2 * e := by
      rw [Polynomial.natDegree_pow, hX2deg]
      ring
    have hcoeff := hmonic.coeff_natDegree
    rwa [hdeg] at hcoeff
  rw [Polynomial.finsetSum_coeff, ← hmain]
  apply Finset.sum_eq_single e
  · intro k hk hke
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hkle : k < e := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hle : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1) ^ k)).natDegree
      ≤ e + k :=
      clearPoly_term_natDegree n k (by omega)
    omega
  · intro hcon
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self e)) hcon

end MetaMathlibExt

namespace MetaMathlibExt

/--
[clearPoly_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma clearPoly_natDegree (n : ℕ) (hn : 2 < n) :
  (clearPoly n).natDegree = 2 * (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree := by
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hle := clearPoly_natDegree_le n
  have hc := clearPoly_coeff n hn
  by_contra hne
  have hlt : (clearPoly n).natDegree < 2 * e := lt_of_le_of_ne hle hne
  have h0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  rw [hc] at h0
  exact one_ne_zero h0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[clearPoly_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma clearPoly_monic (n : ℕ) (hn : 2 < n) : (clearPoly n).Monic := by
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have heq := clearPoly_natDegree n hn
  have hc := clearPoly_coeff n hn
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rwa [heq]

end MetaMathlibExt

/--
[natDegree_realCyclotomicPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma natDegree_realCyclotomicPolynomial_eq
  {n : ℕ}
-- given
  (hn : 2 < n) :
-- imply
  Even n.totient ∧ (realCyclotomicPolynomial n).natDegree = n.totient / 2 := by
-- proof
  apply MetaMathlibExt.natDegree_realCyclotomicPolynomial n hn

/--
[lehmer_cyclotomic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean)
-/
@[path]
private lemma lehmer_cyclotomic_identity_eq
  {n : ℕ}
-- given
  (hn : 2 < n) :
-- imply
  LaurentPolynomial.T (↑(n.totient / 2)) *
    Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
    (realCyclotomicPolynomial n) =
    Polynomial.toLaurent (Polynomial.cyclotomic n ℤ) := by
-- proof
  apply MetaMathlibExt.lehmer_cyclotomic_identity n hn


-- created on 2026-10-20
-- updated on 2026-10-26
