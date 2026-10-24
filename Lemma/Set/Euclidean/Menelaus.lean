import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[affindep_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Menelaus.lean)
-/
@[path]
multiple of the first (and the first is nonzero). -/
private lemma affindep_unique {u v : EuclideanSpace ℝ (Fin 2)} (hu : u ≠ 0)
  (hind : ∀ c : ℝ, c • u ≠ v)
  {a₁ b₁ a₂ b₂ : ℝ} (heq : a₁ • u + b₁ • v = a₂ • u + b₂ • v) :
  a₁ = a₂ ∧ b₁ = b₂ := by
  have h0 : (a₁ - a₂) • u + (b₁ - b₂) • v = 0 := by
    have hsub : (a₁ • u + b₁ • v) - (a₂ • u + b₂ • v) = 0 := sub_eq_zero.mpr heq
    have hexpand : (a₁ • u + b₁ • v) - (a₂ • u + b₂ • v)
      = (a₁ - a₂) • u + (b₁ - b₂) • v := by module
    rwa [hexpand] at hsub
  by_cases hb : b₁ - b₂ = 0
  · have ha : a₁ - a₂ = 0 := by
    have h1 : (a₁ - a₂) • u = 0 := by
      have h := h0
      rwa [hb, zero_smul, add_zero] at h
    obtain h | h := smul_eq_zero.mp h1
    · linarith
    · exact absurd h hu
    exact ⟨by linarith, by linarith⟩
  · exfalso
    have h1 : (b₁ - b₂) • v = (-(a₁ - a₂)) • u := by
      have hexpand : ((a₁ - a₂) • u + (b₁ - b₂) • v) - (a₁ - a₂) • u
        = (b₁ - b₂) • v := by module
      have hexpand2 : (0 : EuclideanSpace ℝ (Fin 2)) - (a₁ - a₂) • u
        = (-(a₁ - a₂)) • u := by module
      have hsub : ((a₁ - a₂) • u + (b₁ - b₂) • v) - (a₁ - a₂) • u
        = 0 - (a₁ - a₂) • u := by rw [h0]
      rwa [hexpand, hexpand2] at hsub
    have key2 : (b₁ - b₂) • v
      = (b₁ - b₂) • ((((b₁ - b₂)⁻¹ * (-(a₁ - a₂))) • u)) := by
      rw [h1, ← mul_smul, mul_inv_cancel_left₀ hb]
    have hcancel : (b₁ - b₂) • (v - (((b₁ - b₂)⁻¹ * (-(a₁ - a₂))) • u)) = 0 := by
      rw [smul_sub, key2, sub_self]
    obtain h | h := smul_eq_zero.mp hcancel
    · exact False.elim (hb h)
    · exact hind _ (sub_eq_zero.mp h).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[menelaus_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Menelaus.lean)
-/
@[path]
lemma menelaus_general
  {A B C D E F : EuclideanSpace ℝ (Fin 2)}
  {AF FB BD DC CE EA : ℝ}
-- given
  (hnc : ¬ ∃ t : ℝ, AffineMap.lineMap A B t = C)
  (hAB : A ≠ B)
  (hFAv : F - A = AF • (B - A))
  (hBFv : B - F = FB • (B - A))
  (hDBv : D - B = BD • (C - B))
  (hCDv : C - D = DC • (C - B))
  (hECv : E - C = CE • (A - C))
  (hAEv : A - E = EA • (A - C))
  (hFB0 : FB ≠ 0)
  (hDC0 : DC ≠ 0)
  (hEA0 : EA ≠ 0) :
-- imply
  (∃ t : ℝ, AffineMap.lineMap D E t = F) ↔ (AF / FB) * (BD / DC) * (CE / EA) = -1 := by
-- proof
  have hBC : B ≠ C := fun h => hnc ⟨1, by rw [AffineMap.lineMap_apply_one, h]⟩
  have hAC : A ≠ C := fun h => hnc ⟨0, by rw [AffineMap.lineMap_apply_zero, h]⟩
  set u : EuclideanSpace ℝ (Fin 2) := B - A with hu_def
  set v : EuclideanSpace ℝ (Fin 2) := C - A with hv_def
  have hu : u ≠ 0 := by
    rw [hu_def]
    exact sub_ne_zero.mpr (Ne.symm hAB)
  have hind : ∀ c : ℝ, c • u ≠ v := by
    intro c hc
    apply hnc
    refine ⟨c, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    have hC : C = A + c • u := by
      rw [hv_def] at hc
      rw [hc, add_sub_cancel]
    rw [hC, hu_def]
    module
  have hCB : C - B ≠ 0 := sub_ne_zero.mpr (Ne.symm hBC)
  have hAC' : A - C ≠ 0 := sub_ne_zero.mpr hAC
  have hsumF : AF + FB = 1 := by
    have h : (AF + FB) • u = (1 : ℝ) • u := by
      rw [add_smul, one_smul, ← hFAv, ← hBFv, hu_def]
      abel
    have h2 : (AF + FB - 1) • u = 0 := by
      have hexpand : (AF + FB - 1) • u = (AF + FB) • u - (1 : ℝ) • u := by module
      rw [hexpand, h, sub_self]
    obtain h3 | h3 := smul_eq_zero.mp h2
    · linarith
    · exact absurd h3 hu
  have hsumD : BD + DC = 1 := by
    have h : (BD + DC) • (C - B) = (1 : ℝ) • (C - B) := by
      rw [add_smul, one_smul, ← hDBv, ← hCDv]
      abel
    have h2 : (BD + DC - 1) • (C - B) = 0 := by
      have hexpand : (BD + DC - 1) • (C - B)
        = (BD + DC) • (C - B) - (1 : ℝ) • (C - B) := by module
      rw [hexpand, h, sub_self]
    obtain h3 | h3 := smul_eq_zero.mp h2
    · linarith
    · exact absurd h3 hCB
  have hsumE : CE + EA = 1 := by
    have h : (CE + EA) • (A - C) = (1 : ℝ) • (A - C) := by
      rw [add_smul, one_smul, ← hECv, ← hAEv]
      abel
    have h2 : (CE + EA - 1) • (A - C) = 0 := by
      have hexpand : (CE + EA - 1) • (A - C)
        = (CE + EA) • (A - C) - (1 : ℝ) • (A - C) := by module
      rw [hexpand, h, sub_self]
    obtain h3 | h3 := smul_eq_zero.mp h2
    · linarith
    · exact absurd h3 hAC'
  have hDA : D - A = (1 - BD) • u + BD • v := by
    have e1 : D - A = (D - B) + (B - A) := by abel
    rw [e1, hDBv, hu_def, hv_def]
    have e2 : (C - B : EuclideanSpace ℝ (Fin 2)) = (C - A) - (B - A) := by abel
    rw [e2]
    module
  have hEA : E - A = (1 - CE) • v := by
    have e : E - A = (E - C) + (C - A) := by abel
    rw [e, hECv, hv_def]
    have eAC : (A - C : EuclideanSpace ℝ (Fin 2)) = (-1 : ℝ) • (C - A) := by module
    rw [eAC]
    module
  have eFB : FB = 1 - AF := by linarith
  have eDC : DC = 1 - BD := by linarith
  have eEA : EA = 1 - CE := by linarith
  constructor
  · rintro ⟨t, ht⟩
    have hline : AffineMap.lineMap D E t = D + t • (E - D) := by
      rw [AffineMap.lineMap_apply_module]
      module
    have hFt : F - D = t • (E - D) := by
      rw [hline] at ht
      have e : D + t • (E - D) - D = t • (E - D) := by abel
      rwa [ht] at e
    have lhs : F - D = (AF - (1 - BD)) • u + (-BD) • v := by
      have eFD : F - D = (F - A) - (D - A) := by abel
      rw [eFD, hFAv, hDA]
      module
    have rhs : t • (E - D) = (-(t * (1 - BD))) • u + (t * ((1 - CE) - BD)) • v := by
      have eED : E - D = (E - A) - (D - A) := by abel
      rw [eED, hEA, hDA]
      module
    rw [lhs, rhs] at hFt
    obtain ⟨hα, hβ⟩ := affindep_unique hu hind hFt
    have elim : (AF - (1 - BD)) * ((1 - CE) - BD) = (1 - BD) * BD := by
      have h2 : (-(t * (1 - BD))) * ((1 - CE) - BD)
        = (1 - BD) * (-(t * ((1 - CE) - BD))) := by ring
      rw [hα, h2, ← hβ, neg_neg]
    simp only [eFB, eDC, eEA] at hFB0 hDC0 hEA0 ⊢
    have hN : AF * BD * CE + (1 - AF) * (1 - BD) * (1 - CE) = 0 := by
      have h := elim
      ring_nf at h ⊢
      linarith
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_iff (mul_ne_zero (mul_ne_zero hFB0 hDC0) hEA0)]
    linear_combination hN
  · intro hprod
    simp only [eFB, eDC, eEA] at hprod hFB0 hDC0 hEA0
    have hne : (1 - AF) * (1 - BD) * (1 - CE) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hFB0 hDC0) hEA0
    have hN : AF * BD * CE + (1 - AF) * (1 - BD) * (1 - CE) = 0 := by
      rw [div_mul_div_comm, div_mul_div_comm, div_eq_iff hne] at hprod
      linear_combination hprod
    have elim : (AF - (1 - BD)) * ((1 - CE) - BD) = (1 - BD) * BD := by
      have h := hN
      ring_nf at h ⊢
      linarith
    have hDC' : (-(1 - BD)) ≠ 0 := neg_ne_zero.mpr hDC0
    set t : ℝ := (AF - (1 - BD)) / (-(1 - BD)) with ht_def
    refine ⟨t, ?_⟩
    have hline : AffineMap.lineMap D E t = D + t • (E - D) := by
      rw [AffineMap.lineMap_apply_module]
      module
    rw [hline]
    have hq : t * (1 - BD) = -(AF - (1 - BD)) := by
      rw [ht_def, div_mul_eq_mul_div, div_eq_iff hDC']
      ring
    have htα : AF - (1 - BD) = -(t * (1 - BD)) := by rw [hq, neg_neg]
    have htβ : -BD = t * ((1 - CE) - BD) := by
      rw [ht_def, div_mul_eq_mul_div, elim]
      have h3 : ((1 - BD) * BD) / (-(1 - BD)) = -BD := by
        rw [div_neg, mul_div_cancel_left₀ BD hDC0]
      rw [h3]
    have eFD : F - D = (F - A) - (D - A) := by abel
    have eED : E - D = (E - A) - (D - A) := by abel
    have lhs : F - D = (AF - (1 - BD)) • u + (-BD) • v := by
      rw [eFD, hFAv, hDA]
      module
    have rhs : t • (E - D) = (-(t * (1 - BD))) • u + (t * ((1 - CE) - BD)) • v := by
      rw [eED, hEA, hDA]
      module
    have hFt : t • (E - D) = F - D := by
      rw [rhs, ← htα, ← htβ, ← lhs]
    rw [hFt, add_sub_cancel]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[menelaus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Menelaus.lean)
-/
@[path]
lemma menelaus
  :
-- imply
  ∀ (A B C D E F : EuclideanSpace ℝ (Fin 2)) (AF FB BD DC CE EA : ℝ),
    (¬ ∃ t : ℝ, AffineMap.lineMap A B t = C) →
    A ≠ B → B ≠ C → A ≠ C →
    (∃ tD : ℝ, AffineMap.lineMap B C tD = D) →
    (∃ tE : ℝ, AffineMap.lineMap C A tE = E) →
    (∃ tF : ℝ, AffineMap.lineMap A B tF = F) →
    D ≠ B → D ≠ C → E ≠ C → E ≠ A → F ≠ A → F ≠ B →
    (F - A = AF • (B - A)) →
    (B - F = FB • (B - A)) →
    (D - B = BD • (C - B)) →
    (C - D = DC • (C - B)) →
    (E - C = CE • (A - C)) →
    (A - E = EA • (A - C)) →
    FB ≠ 0 → DC ≠ 0 → EA ≠ 0 →
    ((∃ t : ℝ, AffineMap.lineMap D E t = F) ↔ (AF / FB) * (BD / DC) * (CE / EA) = -1) := by
-- proof
  intro A B C D E F AF FB BD DC CE EA hnc hAB _ _ _ _ _ _ _ _ _ _ _ hFAv hBFv hDBv hCDv hECv
    hAEv hFB0 hDC0 hEA0
  exact menelaus_general hnc hAB hFAv hBFv hDBv hCDv hECv hAEv hFB0 hDC0 hEA0

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
