import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_smul_vecCons_eq_of_mul_add_mul_eq_zero {K : Type*} [Field K] (a b : K) (x : Fin 2 → K) (hab : a ≠ 0 ∨ b ≠ 0) (h : a * x 0 + b * x 1 = 0) : ∃ c : K, c • Matrix.vecCons b (Matrix.vecCons (-a) Matrix.vecEmpty) = x := by
  if ha : a = 0 then
    have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    have hx1 : x 1 = 0 := by
      rw [ha, zero_mul, zero_add] at h
      apply (mul_eq_zero.mp h).resolve_left hb
    refine ⟨x 0 / b, ?_⟩
    funext k
    fin_cases k
    · simp [div_mul_cancel₀ _ hb]
    · simp [ha, hx1]
  else
    refine ⟨-(x 1) / a, ?_⟩
    funext k
    fin_cases k
    ·
      have hx0 : x 0 = -(b * x 1) / a := by
        field_simp
        linear_combination h
      simp [hx0]
      ring
    · simp [ha]
private lemma mem_span_singleton_of_comp_eq_smul_comp {F F' : Type*} [Field F] [Field F'] (e : F →+* F') {n : Type*} (v w : n → F) (d : F') (h : e ∘ w = d • (e ∘ v)) (hv : v ≠ 0) : w ∈ F ∙ v := by
  obtain ⟨t, ht⟩ : ∃ t, v t ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hv (funext h')
  have het : e (v t) ≠ 0 := (map_ne_zero e).mpr ht
  have hd : d = e (w t / v t) := by
    have h1 := congr_fun h t
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [map_div₀, h1, mul_div_cancel_right₀ _ het]
  refine Submodule.mem_span_singleton.mpr ⟨w t / v t, ?_⟩
  funext s
  apply e.injective
  have h2 := congr_fun h s
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [Pi.smul_apply, smul_eq_mul, map_mul, ← hd, h2]
private lemma mul_comm_of_stableLine_impl {F F' : Type*} [Field F] [Field F'] (e : F →+* F') {ι : Type*} (M : ι → Matrix (Fin 2) (Fin 2) F) (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v) (u : Fin 2 → F') (hu : u ≠ 0) (hstab : ∀ i, ((M i).map e).mulVec u ∈ F' ∙ u) : ∀ i j, M i * M j = M j * M i := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨i, j, hij⟩ := hne
  set N : Matrix (Fin 2) (Fin 2) F := M i * M j - M j * M i with hN
  have hN0 : N ≠ 0 := sub_ne_zero.mpr hij
  obtain ⟨ci, hci⟩ := Submodule.mem_span_singleton.mp (hstab i)
  obtain ⟨cj, hcj⟩ := Submodule.mem_span_singleton.mp (hstab j)
  have hNu : (N.map e).mulVec u = 0 := by
    have hmap : N.map e = (M i).map e * (M j).map e - (M j).map e * (M i).map e := by
      change e.mapMatrix N = e.mapMatrix (M i) * e.mapMatrix (M j) - e.mapMatrix (M j) * e.mapMatrix (M i)
      rw [hN, map_sub, map_mul, map_mul]
    rw [hmap, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hcj, ← hci, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hci, ← hcj, smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, N r 0 ≠ 0 ∨ N r 1 ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hN0
    ext r c
    fin_cases c
    · apply (h' r).1
    · apply (h' r).2
  have hrow : e (N r 0) * u 0 + e (N r 1) * u 1 = 0 := by
    have h1 := congr_fun hNu r
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    apply h1
  have hab : e (N r 0) ≠ 0 ∨ e (N r 1) ≠ 0 := by
    obtain h0 | h1 := hr
    · apply Or.inl ((map_ne_zero e).mpr h0)
    · apply Or.inr ((map_ne_zero e).mpr h1)
  obtain ⟨c, hc⟩ := exists_smul_vecCons_eq_of_mul_add_mul_eq_zero (e (N r 0)) (e (N r 1)) u hab hrow
  set v : Fin 2 → F := Matrix.vecCons (N r 1) (Matrix.vecCons (-N r 0) Matrix.vecEmpty) with hv
  have hev : e ∘ v = Matrix.vecCons (e (N r 1)) (Matrix.vecCons (-e (N r 0)) Matrix.vecEmpty) := by
    funext k
    fin_cases k
    · simp [hv]
    · simp [hv]
  have hcu : c • (e ∘ v) = u := by
    rw [hev]
    apply hc
  have hv0 : v ≠ 0 := by
    intro h0
    obtain h0' | h1' := hr
    ·
      have hfun := congr_fun h0 1
      simp [hv] at hfun
      apply h0' hfun
    ·
      have hfun := congr_fun h0 0
      simp [hv] at hfun
      apply h1' hfun
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcu
    apply hu hcu.symm
  obtain ⟨k, hk⟩ := hirr v hv0
  apply hk
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hstab k)
  have hmv : ((M k).map e).mulVec (e ∘ v) = e ∘ ((M k).mulVec v) := by
    funext t
    apply (RingHom.map_mulVec e (M k) v t).symm
  rw [← hcu, Matrix.mulVec_smul, hmv, smul_comm] at hd
  apply mem_span_singleton_of_comp_eq_smul_comp e v _ d (smul_right_injective _ hc0 hd).symm hv0
/--
[Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span.lean)
-/
@[path]
private lemma main
  [Field F] [Field F']
  (e : F →+* F') (M : ι → Matrix (Fin 2) (Fin 2) F) (u : Fin 2 → F')
  -- given
  (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v)
  (hu : u ≠ 0) (hstab : ∀ i, ((M i).map e).mulVec u ∈ F' ∙ u) :
  -- imply
  ∀ i j, M i * M j = M j * M i := by
  -- proof
  apply mul_comm_of_stableLine_impl (ι := ι) e M hirr u hu hstab


-- created on 2026-10-20
