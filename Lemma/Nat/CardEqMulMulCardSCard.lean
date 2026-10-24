import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma card_eq_three {M : Type u} [CommGroup M] (D N : M →* M) [Finite M] (hDN : ∀ x, D (N x) = 1) : Nat.card M = Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) * Nat.card N.range * Nat.card D.range := by
  have hle : N.range ≤ D.ker := by
    intro _ hx
    obtain ⟨x, rfl⟩ := hx
    apply (MonoidHom.mem_ker).2 (hDN x)
  have h1 : Nat.card M = Nat.card (M ⧸ D.ker) * Nat.card D.ker := Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker
  have h2 : Nat.card (M ⧸ D.ker) = Nat.card D.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv
  have h3 : Nat.card D.ker = Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) * Nat.card (N.range.subgroupOf D.ker) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h4 : Nat.card (N.range.subgroupOf D.ker) = Nat.card N.range := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, h2, h3, h4]
  ring
private lemma finite_case {M : Type u} [CommGroup M] (D N : M →* M) [Finite M] (hDN : ∀ x, D (N x) = 1) (hND : ∀ x, N (D x) = 1) : Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) = Nat.card (N.ker ⧸ (D.range.subgroupOf N.ker)) ∧ Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) ≠ 0 := by
  have hA := card_eq_three D N hDN
  have hB := card_eq_three N D hND
  refine ⟨?_, ?_⟩
  ·
    have hpos : 0 < Nat.card N.range * Nat.card D.range := Nat.mul_pos Nat.card_pos Nat.card_pos
    have : Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) * (Nat.card N.range * Nat.card D.range) = Nat.card (N.ker ⧸ (D.range.subgroupOf N.ker)) * (Nat.card N.range * Nat.card D.range) := by
      rw [← mul_assoc, ← hA, hB]
      ring
    apply Nat.eq_of_mul_eq_mul_right hpos this
  · apply Nat.card_pos.ne'
private noncomputable def quotMap {M : Type u} [CommGroup M] (D : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) : M ⧸ V →* M ⧸ V := QuotientGroup.map V V D (fun v hv => Subgroup.mem_comap.2 (hDV v hv))
@[simp] private lemma quotMap_mk {M : Type u} [CommGroup M] (D : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (x : M) : quotMap D V hDV (x : M ⧸ V) = ((D x : M) : M ⧸ V) := by
  simp [quotMap]
private lemma quotMap_comp {M : Type u} [CommGroup M] (D N : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V) (hDN : ∀ x, D (N x) = 1) (q : M ⧸ V) : quotMap D V hDV (quotMap N V hNV q) = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  simp [hDN]
private noncomputable def kerToQuot {M : Type u} [CommGroup M] (D : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) : D.ker →* (quotMap D V hDV).ker where
  toFun x := ⟨((x : M) : M ⧸ V), by rw [MonoidHom.mem_ker, quotMap_mk, (MonoidHom.mem_ker).1 x.2, QuotientGroup.mk_one]⟩
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp
private lemma kerToQuot_coe {M : Type u} [CommGroup M] (D : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (x : D.ker) : ((kerToQuot D V hDV x : (quotMap D V hDV).ker) : M ⧸ V) = ((x : M) : M ⧸ V) := rfl
private lemma tateMap_spec {M : Type u} [CommGroup M] (D N : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V) : N.range.subgroupOf D.ker ≤ ((quotMap N V hNV).range.subgroupOf (quotMap D V hDV).ker).comap (kerToQuot D V hDV) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨y, hy⟩ := hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, kerToQuot_coe]
  exact ⟨(y : M ⧸ V), by rw [quotMap_mk, hy]⟩
private noncomputable def tateMap {M : Type u} [CommGroup M] (D N : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V) : D.ker ⧸ (N.range.subgroupOf D.ker) →* (quotMap D V hDV).ker ⧸ ((quotMap N V hNV).range.subgroupOf (quotMap D V hDV).ker) := QuotientGroup.map _ _ (kerToQuot D V hDV) (tateMap_spec D N V hDV hNV)
private lemma tateMap_injective {M : Type u} [CommGroup M] (D N : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V) (hDN : ∀ x, D (N x) = 1) (h0 : ∀ v ∈ V, D v = 1 → ∃ w ∈ V, N w = v) : Function.Injective (tateMap D N V hDV hNV) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hq' : ((kerToQuot D V hDV x : (quotMap D V hDV).ker) : (quotMap D V hDV).ker ⧸ ((quotMap N V hNV).range.subgroupOf (quotMap D V hDV).ker)) = 1 := by
    simpa [tateMap] using hq
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, kerToQuot_coe] at hq'
  obtain ⟨q', hq'⟩ := hq'
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q'
  rw [quotMap_mk, QuotientGroup.eq] at hq'
  have hDv : D ((N m)⁻¹ * (x : M)) = 1 := by
    rw [map_mul, map_inv, hDN, inv_one, one_mul]
    apply (MonoidHom.mem_ker).1 x.2
  obtain ⟨w, _, hw⟩ := h0 _ hq' hDv
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨m * w, ?_⟩
  rw [map_mul, hw, mul_inv_cancel_left]
private lemma tateMap_surjective {M : Type u} [CommGroup M] (D N : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V) (hND : ∀ x, N (D x) = 1) (h1 : ∀ v ∈ V, N v = 1 → ∃ w ∈ V, D w = v) : Function.Surjective (tateMap D N V hDV hNV) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, hy⟩ := y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MonoidHom.mem_ker, quotMap_mk, QuotientGroup.eq_one_iff] at hy
  obtain ⟨w, hwV, hw⟩ := h1 _ hy (hND m)
  have hker : m * w⁻¹ ∈ D.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hw, mul_inv_cancel]
  refine ⟨((⟨m * w⁻¹, hker⟩ : D.ker) : D.ker ⧸ (N.range.subgroupOf D.ker)), ?_⟩
  simp only [tateMap, QuotientGroup.map_mk]
  congr 1
  ext
  simp only [kerToQuot_coe]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff w).2 hwV, inv_one, mul_one]
private lemma card_tate_eq {M : Type u} [CommGroup M] (D N : M →* M) (V : Subgroup M) (hDV : ∀ v ∈ V, D v ∈ V) (hNV : ∀ v ∈ V, N v ∈ V) (hDN : ∀ x, D (N x) = 1) (hND : ∀ x, N (D x) = 1) (h0 : ∀ v ∈ V, D v = 1 → ∃ w ∈ V, N w = v) (h1 : ∀ v ∈ V, N v = 1 → ∃ w ∈ V, D w = v) : Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) = Nat.card ((quotMap D V hDV).ker ⧸ ((quotMap N V hNV).range.subgroupOf (quotMap D V hDV).ker)) := Nat.card_congr (Equiv.ofBijective _ ⟨tateMap_injective D N V hDV hNV hDN h0, tateMap_surjective D N V hDV hNV hND h1⟩)
/--
[M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex.lean)
-/
@[path]
private lemma main
  {M : Type u} [CommGroup M]
  (D N : M →* M)
  (V : Subgroup M) [V.FiniteIndex]
  -- given
  (hDN : ∀ x, D (N x) = 1)
  (hND : ∀ x, N (D x) = 1)
  (hDV : ∀ v ∈ V, D v ∈ V)
  (hNV : ∀ v ∈ V, N v ∈ V)
  (h0 : ∀ v ∈ V, D v = 1 → ∃ w ∈ V, N w = v)
  (h1 : ∀ v ∈ V, N v = 1 → ∃ w ∈ V, D w = v) :
  -- imply
  Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) = Nat.card (N.ker ⧸ (D.range.subgroupOf N.ker)) ∧ Nat.card (D.ker ⧸ (N.range.subgroupOf D.ker)) ≠ 0 := by
  -- proof
  have e0 := card_tate_eq D N V hDV hNV hDN hND h0 h1
  have e1 := card_tate_eq N D V hNV hDV hND hDN h1 h0
  rw [e0, e1]
  apply finite_case (quotMap D V hDV) (quotMap N V hNV) (quotMap_comp D N V hDV hNV hDN) (quotMap_comp N D V hNV hDV hND)


-- created on 2026-10-20
