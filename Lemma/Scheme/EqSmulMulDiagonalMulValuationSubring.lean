import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev v2 {α : Type} (a b : α) : Fin 2 → α := Matrix.vecCons a (Matrix.vecCons b Matrix.vecEmpty)
private abbrev m2 {α : Type} (a b c d : α) : Matrix (Fin 2) (Fin 2) α := Matrix.of (Matrix.vecCons (v2 a b) (Matrix.vecCons (v2 c d) Matrix.vecEmpty))
private noncomputable def IsInt [Field K] (O : ValuationSubring K) (k : GL (Fin 2) K) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧ (∀ i j, ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O)
private lemma mul_entry_mem [Field K] (O : ValuationSubring K) {A B : Matrix (Fin 2) (Fin 2) K} (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (i j : Fin 2) : (A * B) i j ∈ O := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact O.add_mem _ _ (O.mul_mem _ _ (hA _ _) (hB _ _)) (O.mul_mem _ _ (hA _ _) (hB _ _))
private lemma IsInt.mul [Field K] (O : ValuationSubring K) {k k' : GL (Fin 2) K} (hk : IsInt O k) (hk' : IsInt O k') : IsInt O (k * k') := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  ·
    rw [Units.val_mul]
    exact mul_entry_mem O hk.1 hk'.1 i j
  ·
    rw [_root_.mul_inv_rev, Units.val_mul]
    exact mul_entry_mem O hk'.2 hk.2 i j
private noncomputable def mkGL [Field K] (A B : Matrix (Fin 2) (Fin 2) K) (h1 : A * B = 1) (h2 : B * A = 1) : GL (Fin 2) K := ⟨A, B, h1, h2⟩
@[simp] private lemma coe_mkGL [Field K] (A B : Matrix (Fin 2) (Fin 2) K) (h1 : A * B = 1) (h2 : B * A = 1) : ((mkGL A B h1 h2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A := rfl
@[simp] private lemma coe_mkGL_inv [Field K] (A B : Matrix (Fin 2) (Fin 2) K) (h1 : A * B = 1) (h2 : B * A = 1) : (((mkGL A B h1 h2)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = B := rfl
private lemma lower_mul [Field K] (c : K) : m2 (1 : K) 0 c 1 * m2 1 0 (-c) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
private lemma lower_mul_inv [Field K] (c : K) : m2 (1 : K) 0 (-c) 1 * m2 1 0 c 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
private noncomputable def lower [Field K] (c : K) : GL (Fin 2) K := mkGL (m2 1 0 c 1) (m2 1 0 (-c) 1) (lower_mul c) (lower_mul_inv c)
private lemma upper_mul [Field K] (b : K) : m2 (1 : K) b 0 1 * m2 1 (-b) 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
private lemma upper_mul_inv [Field K] (b : K) : m2 (1 : K) (-b) 0 1 * m2 1 b 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
private noncomputable def upper [Field K] (b : K) : GL (Fin 2) K := mkGL (m2 1 b 0 1) (m2 1 (-b) 0 1) (upper_mul b) (upper_mul_inv b)
private lemma swap_mul [Field K] : m2 (0 : K) 1 1 0 * m2 0 1 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
private noncomputable def swap [Field K] : GL (Fin 2) K := mkGL (m2 0 1 1 0) (m2 0 1 1 0) swap_mul swap_mul
@[simp] private lemma coe_lower [Field K] (c : K) : ((lower c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = m2 1 0 c 1 := rfl
@[simp] private lemma coe_lower_inv [Field K] (c : K) : (((lower c)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = m2 1 0 (-c) 1 := rfl
@[simp] private lemma coe_upper [Field K] (b : K) : ((upper b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = m2 1 b 0 1 := rfl
@[simp] private lemma coe_upper_inv [Field K] (b : K) : (((upper b)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = m2 1 (-b) 0 1 := rfl
@[simp] private lemma coe_swap [Field K] : ((swap : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = m2 0 1 1 0 := rfl
@[simp] private lemma coe_swap_inv [Field K] : ((swap⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = m2 0 1 1 0 := rfl
private lemma isInt_lower [Field K] (O : ValuationSubring K) {c : K} (hc : c ∈ O) : IsInt O (lower c) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  ·
    rw [coe_lower]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, hc]
  ·
    rw [coe_lower_inv]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, O.neg_mem _ hc]
private lemma isInt_upper [Field K] (O : ValuationSubring K) {b : K} (hb : b ∈ O) : IsInt O (upper b) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  ·
    rw [coe_upper]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, hb]
  ·
    rw [coe_upper_inv]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem, O.neg_mem _ hb]
private lemma isInt_swap [Field K] (O : ValuationSubring K) : IsInt O (swap : GL (Fin 2) K) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  ·
    rw [coe_swap]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]
  ·
    rw [coe_swap_inv]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]
private lemma isInt_one [Field K] (O : ValuationSubring K) : IsInt O (1 : GL (Fin 2) K) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  ·
    rw [Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]
  ·
    rw [inv_one, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]
private noncomputable def Concl [Field K] (O : ValuationSubring K) (A : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧ IsInt O k₁ ∧ IsInt O k₂ ∧ A = s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal (v2 (1 : K) t) * (k₂ : Matrix (Fin 2) (Fin 2) K))
private lemma base [Field K] (O : ValuationSubring K) (a b c d : K) (ha : a ≠ 0) (hb : b / a ∈ O) (hc : c / a ∈ O) (hd : d / a ∈ O) (hdet : a * d - b * c ≠ 0) : Concl O (m2 a b c d) := by
  refine ⟨a, d / a - (c / a) * (b / a), lower (c / a), upper (b / a), ha, ?_, ?_, isInt_lower O hc, isInt_upper O hb, ?_⟩
  ·
    have h : d / a - (c / a) * (b / a) = (a * d - b * c) / a ^ 2 := by field_simp
    rw [h]
    refine div_ne_zero hdet (pow_ne_zero 2 ha)
  · exact O.toSubring.sub_mem hd (O.mul_mem _ _ hc hb)
  ·
    have hD : Matrix.diagonal (v2 (1 : K) (d / a - c / a * (b / a))) = m2 1 0 0 (d / a - c / a * (b / a)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [coe_lower, coe_upper, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp; try (field_simp; try ring))
private lemma of_conj [Field K] (O : ValuationSubring K) {H A : Matrix (Fin 2) (Fin 2) K} {P Q : GL (Fin 2) K} (hP : IsInt O P) (hQ : IsInt O Q) (hHA : H = (P : Matrix (Fin 2) (Fin 2) K) * A * (Q : Matrix (Fin 2) (Fin 2) K)) (hA : Concl O A) : Concl O H := by
  obtain ⟨s, t, k₁, k₂, hs, ht, htO, hk₁, hk₂, hAeq⟩ := hA
  refine ⟨s, t, P * k₁, k₂ * Q, hs, ht, htO, hP.mul O hk₁, hk₂.mul O hQ, ?_⟩
  rw [hHA, hAeq, Units.val_mul, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
private lemma exists_entry_dvd [Field K] (O : ValuationSubring K) (A : Matrix (Fin 2) (Fin 2) K) (hA : ∃ i j, A i j ≠ 0) : ∃ i₀ j₀, A i₀ j₀ ≠ 0 ∧ ∀ i j, A i j / A i₀ j₀ ∈ O := by
  classical
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2)) (fun ij => O.valuation (A ij.1 ij.2)) Finset.univ_nonempty
  have h0 : A i₀ j₀ ≠ 0 := by
    obtain ⟨i, j, hij⟩ := hA
    intro h0
    have h := hmax (i, j) (Finset.mem_univ _)
    simp only [h0, map_zero, le_zero_iff] at h
    exact hij ((Valuation.zero_iff _).mp h)
  refine ⟨i₀, j₀, h0, fun i j => ?_⟩
  rw [← O.valuation_le_one_iff, map_div₀]
  have hpos : 0 < O.valuation (A i₀ j₀) := (Valuation.pos_iff _).mpr h0
  rw [div_le_one₀ hpos]
  exact hmax (i, j) (Finset.mem_univ _)
private lemma concl [Field K] (O : ValuationSubring K) (H : GL (Fin 2) K) : Concl O (H : Matrix (Fin 2) (Fin 2) K) := by
  set A : Matrix (Fin 2) (Fin 2) K := (H : Matrix (Fin 2) (Fin 2) K) with hAdef
  have hdet : A.det ≠ 0 := by
    rw [hAdef, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_fin_two] at hdet
  have hne : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    simp [h]
  obtain ⟨i₀, j₀, h0, hdiv⟩ := exists_entry_dvd O A hne
  have hA : A = m2 (A 0 0) (A 0 1) (A 1 0) (A 1 1) := Matrix.eta_fin_two A
  fin_cases i₀ <;> fin_cases j₀
  ·
    simp only [Fin.zero_eta, Fin.isValue] at h0 hdiv
    rw [hA]
    exact base O _ _ _ _ h0 (hdiv 0 1) (hdiv 1 0) (hdiv 1 1) hdet
  ·
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at h0 hdiv
    refine of_conj O (P := 1) (Q := swap) (isInt_one O) (isInt_swap O) (A := m2 (A 0 1) (A 0 0) (A 1 1) (A 1 0)) ?_ ?_
    ·
      rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ·
      refine base O _ _ _ _ h0 (hdiv 0 0) (hdiv 1 1) (hdiv 1 0) ?_
      intro h
      apply hdet
      linear_combination -h
  ·
    simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue] at h0 hdiv
    refine of_conj O (P := swap) (Q := 1) (isInt_swap O) (isInt_one O) (A := m2 (A 1 0) (A 1 1) (A 0 0) (A 0 1)) ?_ ?_
    ·
      rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ·
      refine base O _ _ _ _ h0 (hdiv 1 1) (hdiv 0 0) (hdiv 0 1) ?_
      intro h
      apply hdet
      linear_combination -h
  ·
    simp only [Fin.mk_one, Fin.isValue] at h0 hdiv
    refine of_conj O (P := swap) (Q := swap) (isInt_swap O) (isInt_swap O) (A := m2 (A 1 1) (A 1 0) (A 0 1) (A 0 0)) ?_ ?_
    ·
      rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ·
      refine base O _ _ _ _ h0 (hdiv 1 0) (hdiv 0 1) (hdiv 0 0) ?_
      intro h
      apply hdet
      linear_combination h
/--
[Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.lean)
-/
@[path]
private lemma main
  [Field K]
  (O : ValuationSubring K)
  (H : GL (Fin 2) K) :
  -- imply
  ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧ (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧ (∀ i j, ((k₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧ (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧ (∀ i j, ((k₂⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧ (H : Matrix (Fin 2) (Fin 2) K) = s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal (v2 (1 : K) t) * (k₂ : Matrix (Fin 2) (Fin 2) K)) := by
  -- proof
  obtain ⟨s, t, k₁, k₂, hs, ht, htO, hk₁, hk₂, heq⟩ := concl O H
  exact ⟨s, t, k₁, k₂, hs, ht, htO, hk₁.1, hk₁.2, hk₂.1, hk₂.2, heq⟩


-- created on 2026-10-20
