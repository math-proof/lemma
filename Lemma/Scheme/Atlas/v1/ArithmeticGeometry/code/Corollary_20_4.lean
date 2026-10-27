import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.ArithmeticGeometry.code.Corollary_20_4
open Finset


/--
[val_zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma val_zero_mem
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {x : F}
-- given
  (hv : ∀ i, v i x = (0 : ℤ)) :
-- imply
  x ∈ DVRIntersection n v := by
-- proof
  intro i; rw [hv i]; exact le_refl _

/--
[val_zero_inv_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma val_zero_inv_mem
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {x : F}
-- given
  (hv : ∀ i, v i x = (0 : ℤ)) :
-- imply
  x⁻¹ ∈ DVRIntersection n v := by
-- proof
  intro i; rw [AddValuation.map_inv, hv i]; simp

/--
[isUnit_of_val_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma isUnit_of_val_zero
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {x : F}
-- given
  (hx : x ≠ 0)
  (hv : ∀ i, v i x = (0 : ℤ)) :
-- imply
  IsUnit (⟨x, val_zero_mem hv⟩ : DVRIntersection n v) := by
-- proof
  rw [isUnit_iff_exists_inv]
  refine ⟨⟨x⁻¹, val_zero_inv_mem hv⟩, ?_⟩
  ext; simp [mul_inv_cancel₀ hx]

/--
[val_nonneg_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma val_nonneg_int
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {x : F}
  {i : Fin n}
-- given
  (hx : x ≠ 0)
  (hmem : x ∈ DVRIntersection n v) :
-- imply
  ∃ a : ℕ, v i x = ((a : ℤ) : WithTop ℤ) := by
-- proof
  have hne : v i x ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
  set c := (v i x).untop hne
  have hc : v i x = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
  have hnn : 0 ≤ c := by
    have := hmem i; rw [hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at this; exact this
  exact ⟨c.toNat, by rw [hc]; congr 1; omega⟩

/--
[not_isUnit_of_inv_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma not_isUnit_of_inv_not_mem
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {x : F}
-- given
  (hx_mem : x ∈ DVRIntersection n v)
  (hxi_not_mem : x⁻¹ ∉ DVRIntersection n v) :
-- imply
  ¬IsUnit (⟨x, hx_mem⟩ : DVRIntersection n v) := by
-- proof
  intro ⟨u, hu⟩
  apply hxi_not_mem
  have h1 : (↑u : DVRIntersection n v).val = x := congr_arg Subtype.val hu
  have h3 : x * (↑(u⁻¹) : DVRIntersection n v).val = 1 := by
    have h2 := congr_arg (fun r => (r : DVRIntersection n v).val) u.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at h2
    rwa [h1] at h2
  have h4 : (↑(u⁻¹) : DVRIntersection n v).val = x⁻¹ :=
    eq_comm.mpr (inv_eq_of_mul_eq_one_right h3)
  rw [← h4]; exact (↑(u⁻¹) : DVRIntersection n v).prop

/--
[withtop_neg_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma withtop_neg_coe
  [Field F]
  {a : ℤ} :
-- imply
  -(↑a : WithTop ℤ) = ((-a : ℤ) : WithTop ℤ) :=
-- proof
  (WithTop.LinearOrderedAddCommGroup.coe_neg a).symm

/--
[withtop_coe_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma withtop_coe_nonneg
  [Field F]
  {a : ℤ}
-- given
  (ha : 0 ≤ a) :
-- imply
  (0 : WithTop ℤ) ≤ (a : WithTop ℤ) := by
-- proof
  rw [← WithTop.coe_zero, WithTop.coe_le_coe]; exact ha

/--
[withtop_not_nonneg_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma withtop_not_nonneg_neg_one
  [Field F]
-- given
  (h : (0 : WithTop ℤ) ≤ -(1 : WithTop ℤ)) :
-- imply
  False := by
-- proof
  have h1 : -(1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by norm_num
  rw [h1, ← WithTop.coe_zero, WithTop.coe_le_coe] at h; omega

/--
[uniformizer_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma uniformizer_mem
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {j : Fin n}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0)) :
-- imply
  t j ∈ DVRIntersection n v := by
-- proof
  intro i
  by_cases hij : i = j
  · subst hij; rw [ht i i, if_pos rfl]; exact withtop_coe_nonneg (by omega)
  · rw [ht i j, if_neg hij]; exact le_refl _

/--
[uniformizer_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma uniformizer_ne_zero
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {j : Fin n}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0)) :
-- imply
  t j ≠ 0 := by
-- proof
  intro hj
  have := ht j j; simp at this; rw [hj, AddValuation.map_zero] at this; simp at this

/--
[uniformizer_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma uniformizer_prime
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {j : Fin n}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0)) :
-- imply
  Prime (⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v) := by
-- proof
  have ht_ne := uniformizer_ne_zero ht
  have ht_mem := uniformizer_mem ht
  have ht_self : ∀ k, v k (t k) = (1 : ℤ) := by
    intro k; have := ht k k; simp at this; exact this
  refine ⟨fun h => ht_ne j (congr_arg Subtype.val h), ?_, ?_⟩
  ·
    apply not_isUnit_of_inv_not_mem (ht_mem j)
    intro hmem
    have h1 : (0 : WithTop ℤ) ≤ v j (t j)⁻¹ := hmem j
    rw [AddValuation.map_inv, ht_self j] at h1
    exact withtop_not_nonneg_neg_one h1
  ·
    intro ⟨a', ha'_mem⟩ ⟨b', hb'_mem⟩ ⟨⟨c, hc_mem⟩, hc⟩
    have hc_F := congr_arg Subtype.val hc
    simp only [Subring.coe_mul] at hc_F
    by_cases ha'_zero : a' = 0
    · left; exact ⟨⟨0, (DVRIntersection n v).zero_mem⟩, Subtype.ext (by simp [ha'_zero])⟩
    by_cases hb'_zero : b' = 0
    · right; exact ⟨⟨0, (DVRIntersection n v).zero_mem⟩, Subtype.ext (by simp [hb'_zero])⟩
    obtain ⟨ea, hea⟩ := val_nonneg_int ha'_zero ha'_mem j
    obtain ⟨eb, heb⟩ := val_nonneg_int hb'_zero hb'_mem j
    have hab_val : v j (a' * b') = ((ea + eb : ℤ) : WithTop ℤ) := by
      rw [(v j).map_mul, hea, heb, ← WithTop.coe_add]
    have hc_ne : c ≠ 0 := by
      intro h; rw [h, mul_zero] at hc_F; exact (mul_ne_zero ha'_zero hb'_zero) hc_F
    obtain ⟨ec, hec⟩ := val_nonneg_int hc_ne hc_mem j
    have htc_val : v j (t j * c) = ((1 + ec : ℤ) : WithTop ℤ) := by
      rw [(v j).map_mul, ht_self j, hec, ← WithTop.coe_add]
    have hab_eq : (ea : ℤ) + eb = 1 + ec := by
      have := congr_arg (v j) hc_F; rw [hab_val, htc_val] at this
      exact WithTop.coe_injective this
    obtain hea0 | hea_pos := Nat.eq_zero_or_pos ea
    · right
      have heb1 : 1 ≤ eb := by omega
      have hq_mem : b' * (t j)⁻¹ ∈ DVRIntersection n v := by
        intro i; rw [(v i).map_mul, AddValuation.map_inv, ht i j]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, heb, withtop_neg_coe, ← WithTop.coe_add, ← WithTop.coe_zero,
          WithTop.coe_le_coe]; omega
        · rw [if_neg hij]; simp [neg_zero]; exact hb'_mem i
      exact ⟨⟨b' * (t j)⁻¹, hq_mem⟩, Subtype.ext (by
        simp only [Subring.coe_mul]
        rw [mul_comm (t j), mul_assoc, inv_mul_cancel₀ (ht_ne j), mul_one])⟩
    · left
      have hq_mem : a' * (t j)⁻¹ ∈ DVRIntersection n v := by
        intro i; rw [(v i).map_mul, AddValuation.map_inv, ht i j]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, hea, withtop_neg_coe, ← WithTop.coe_add, ← WithTop.coe_zero,
          WithTop.coe_le_coe]; omega
        · rw [if_neg hij]; simp [neg_zero]; exact ha'_mem i
      exact ⟨⟨a' * (t j)⁻¹, hq_mem⟩, Subtype.ext (by
        simp only [Subring.coe_mul]
        rw [mul_comm (t j), mul_assoc, inv_mul_cancel₀ (ht_ne j), mul_one])⟩

/--
[uniformizer_ideal_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma uniformizer_ideal_isPrime
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {j : Fin n}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0)) :
-- imply
  (Ideal.span {(⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v)}).IsPrime := by
-- proof
  rw [Ideal.span_singleton_prime (show (⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v) ≠ 0
    from fun h => uniformizer_ne_zero ht j (congr_arg Subtype.val h))]
  exact uniformizer_prime ht j

/--
[dvr_intersection_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma dvr_intersection_factorization
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {a : F}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
  (ha_ne : a ≠ 0)
  (ha_mem : a ∈ DVRIntersection n v) :
-- imply
  ∃ (e : Fin n → ℕ) (u : (DVRIntersection n v)ˣ), (∀ i, v i a = ((e i : ℤ) : WithTop ℤ)) ∧ (⟨a, ha_mem⟩ : DVRIntersection n v) = ↑u * ∏ j : Fin n, (⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v) ^ e j := by
-- proof
  have ht_ne := uniformizer_ne_zero ht
  have ht_mem := uniformizer_mem ht
  have ht_self : ∀ k, v k (t k) = (1 : ℤ) := by
    intro k; have := ht k k; simp at this; exact this
  choose e he using fun i => val_nonneg_int ha_ne ha_mem i
  set prod_t := ∏ j : Fin n, (t j) ^ (e j) with hprod_t_def
  have hprod_ne : prod_t ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (ht_ne i))
  have hval_prod : ∀ i, v i prod_t = ((e i : ℤ) : WithTop ℤ) := by
    intro i; rw [hprod_t_def, addval_prod]
    simp_rw [fun j => addval_npow_coe (v i) (e j) (ht i j), mul_ite, mul_one, mul_zero]
    rw [show ∑ x : Fin n, (↑(if i = x then (e x : ℤ) else 0) : WithTop ℤ) =
      ↑(∑ x : Fin n, (if i = x then (e x : ℤ) else 0)) from by rw [WithTop.coe_sum]]
    congr 1; simp [Finset.mem_univ]
  set u_F := a * prod_t⁻¹ with hu_def
  have hu_ne : u_F ≠ 0 := mul_ne_zero ha_ne (inv_ne_zero hprod_ne)
  have hval_u : ∀ i, v i u_F = (0 : ℤ) := by
    intro i; rw [hu_def, (v i).map_mul, AddValuation.map_inv, he i, hval_prod i]; simp
  have hu_unit : IsUnit (⟨u_F, val_zero_mem hval_u⟩ : DVRIntersection n v) :=
    isUnit_of_val_zero hu_ne hval_u
  have hprod_mem : prod_t ∈ DVRIntersection n v := by
    intro i; rw [hval_prod i]; exact withtop_coe_nonneg (Int.natCast_nonneg _)
  have ha_eq : a = u_F * prod_t := by
    rw [hu_def, mul_assoc, inv_mul_cancel₀ hprod_ne, mul_one]
  obtain ⟨w, hw⟩ := hu_unit
  refine ⟨e, w, he, ?_⟩
  apply Subtype.ext
  simp only [Subring.coe_mul, SubmonoidClass.coe_finset_prod, Subring.coe_pow]
  rw [ha_eq]
  congr 1
  exact (congr_arg Subtype.val hw).symm

/--
[mem_uniformizer_ideal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma mem_uniformizer_ideal_iff
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {j : Fin n}
  {x : DVRIntersection n v}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0)) :
-- imply
  x ∈ Ideal.span {(⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v)} ↔ (1 : WithTop ℤ) ≤ v j x.val := by
-- proof
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨⟨y, hy_mem⟩, rfl⟩
    simp only [Subring.coe_mul]
    rw [(v j).map_mul]
    have htj : v j (t j) = (1 : ℤ) := by have := ht j j; simp at this; exact this
    rw [htj]
    have hnn : (0 : WithTop ℤ) ≤ v j y := hy_mem j
    rw [← WithTop.coe_one]
    obtain rfl | hy_ne := eq_or_ne y 0
    · simp [AddValuation.map_zero]
    · have hne : v j y ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
      set c := (v j y).untop hne
      have hc : v j y = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
      rw [hc, ← WithTop.coe_add, WithTop.coe_le_coe]
      rw [hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at hnn
      omega
  · intro hval
    by_cases hx : x.val = 0
    · exact ⟨0, Subtype.ext (by simp [hx])⟩
    · have hq_mem : x.val * (t j)⁻¹ ∈ DVRIntersection n v := by
      intro i
      rw [(v i).map_mul, AddValuation.map_inv, ht i j]
      by_cases hij : i = j
      · rw [hij, if_pos rfl]
        have hne : v j x.val ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
        set c := (v j x.val).untop hne
        have hc_eq : v j x.val = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
        rw [hc_eq, withtop_neg_coe, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
        rw [hc_eq, ← WithTop.coe_one, WithTop.coe_le_coe] at hval
        omega
      · rw [if_neg hij]; simp [neg_zero]; exact x.prop i
      exact ⟨⟨x.val * (t j)⁻¹, hq_mem⟩, Subtype.ext (by
        simp only [Subring.coe_mul]
        rw [mul_comm (t j), mul_assoc, inv_mul_cancel₀ (uniformizer_ne_zero ht j), mul_one])⟩

/--
[nonunit_in_some_uniformizer_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean)
-/
@[path]
lemma nonunit_in_some_uniformizer_ideal
  [Field F]
  {n : ℕ}
  {v : Fin n → AddValuation F (WithTop ℤ)}
  {t : Fin n → F}
  {x : DVRIntersection n v}
-- given
  (ht : ∀ i j, v i (t j) = ↑(if i = j then (1 : ℤ) else 0))
  (hx_ne : x ≠ 0)
  (hx_nu : ¬IsUnit x) :
-- imply
  ∃ j : Fin n, x ∈ Ideal.span {(⟨t j, uniformizer_mem ht j⟩ : DVRIntersection n v)} := by
-- proof
  by_contra h
  push_neg at h
  have hx_ne_F : x.val ≠ 0 := fun habs => hx_ne (Subtype.ext habs)
  have hval_zero : ∀ j, v j x.val = (0 : ℤ) := by
    intro j
    have hnotmem := h j
    rw [mem_uniformizer_ideal_iff ht j x] at hnotmem
    push_neg at hnotmem
    have hne : v j x.val ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
    set c := (v j x.val).untop hne
    have hc : v j x.val = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
    have hnn : 0 ≤ c := by
      have := x.prop j; rw [hc, ← WithTop.coe_zero, WithTop.coe_le_coe] at this; exact this
    have hlt : c < 1 := by
      rw [hc, ← WithTop.coe_one, WithTop.coe_lt_coe] at hnotmem; exact hnotmem
    rw [hc]; congr 1; omega
  exact hx_nu (isUnit_of_val_zero hx_ne_F hval_zero)


-- created on 2026-10-23
