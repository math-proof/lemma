import Lemma.LanglandsTunnell.CubicInduction_PrincipalSeries3
import Lemma.LanglandsTunnell.StandardLocalConstantsAt
import Def.LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section Jacquet

variable (v : HeightOneSpectrum (𝓞 ℚ))


theorem mem_unipotentBall3_iff (c : ℤ) (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    p ∈ unipotentBall3 v c ↔
      Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c) :=
  Iff.rfl

theorem unipotentBall3_mono {c c' : ℤ} (h : c ≤ c') : unipotentBall3 v c ⊆ unipotentBall3 v c' := by
  intro p hp
  simp only [mem_unipotentBall3_iff] at hp ⊢
  exact ⟨hp.1.trans (WithZero.exp_le_exp.mpr h), hp.2.1.trans (WithZero.exp_le_exp.mpr h),
    hp.2.2.trans (WithZero.exp_le_exp.mpr (by omega))⟩

theorem upperUnipotent3_mul_upperUnipotent3 {A : Type*} [CommRing A] (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem upperUnipotent3_inv_eq {A : Type*} [CommRing A] (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, upperUnipotent3_mul_upperUnipotent3, show x + -x = 0 by ring,
    show y + -y = 0 by ring, show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

theorem unipotentBall3_mul_mem {c : ℤ} {p p' : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (hp : p ∈ unipotentBall3 v c) (hp' : p' ∈ unipotentBall3 v c) :
    (p.1 + p'.1, p.2.1 + p'.2.1, p.2.2 + p'.2.2 + p.1 * p'.2.1) ∈ unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff] at hp hp' ⊢
  refine ⟨(Valuation.map_add _ _ _).trans (max_le hp.1 hp'.1),
    (Valuation.map_add _ _ _).trans (max_le hp.2.1 hp'.2.1), ?_⟩
  refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le hp.2.2 hp'.2.2)) ?_)
  rw [Valuation.map_mul, two_mul, WithZero.exp_add]
  exact mul_le_mul' hp.1 hp'.2.1

theorem unipotentBall3_inv_mem {c : ℤ} {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ}
    (hp : p ∈ unipotentBall3 v c) : (-p.1, -p.2.1, p.1 * p.2.1 - p.2.2) ∈ unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff] at hp ⊢
  refine ⟨by rw [Valuation.map_neg]; exact hp.1, by rw [Valuation.map_neg]; exact hp.2.1, ?_⟩
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ hp.2.2)
  rw [Valuation.map_mul, two_mul, WithZero.exp_add]
  exact mul_le_mul' hp.1 hp.2.1

theorem zero_mem_unipotentBall3 (c : ℤ) :
    ((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ)) ∈ unipotentBall3 v c := by
  simp only [mem_unipotentBall3_iff, Valuation.map_zero]
  exact ⟨zero_le', zero_le', zero_le'⟩


theorem psiLoc_stdAddChar : psiLoc (stdAddChar ℚ) v = psiLocal ℚ v :=
  rfl


theorem jacquetTruncated3_add (c : ℤ) (u u' : LocalGL3 v → ℂ)
    (hu : letI := localBorel ℚ v; IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
        (unipotentBall3 v c) (jacquetHaar3 v))
    (hu' : letI := localBorel ℚ v; IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u' (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
        (unipotentBall3 v c) (jacquetHaar3 v)) :
    jacquetTruncated3 v c (u + u') = jacquetTruncated3 v c u + jacquetTruncated3 v c u' := by
  letI := localBorel ℚ v
  simp only [jacquetTruncated3, Pi.add_apply, mul_add]
  exact integral_add hu hu'

theorem jacquetTruncated3_smul (c : ℤ) (a : ℂ) (u : LocalGL3 v → ℂ) :
    jacquetTruncated3 v c (a • u) = a * jacquetTruncated3 v c u := by
  letI := localBorel ℚ v
  simp only [jacquetTruncated3, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring


theorem jacquetTruncated3_eq_jacquetValue (u : LocalGL3 v → ℂ)
    (h : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u) {c : ℤ}
    (hc : (jacquetLevel v u : ℤ) ≤ c) : jacquetTruncated3 v c u = jacquetValue v u := by
  have hmem : jacquetLevel v u ∈
      {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u} :=
    Nat.sInf_mem h
  exact hmem c hc

theorem jacquetLevel_le (u : LocalGL3 v → ℂ) {c₀ : ℕ}
    (h : ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u) :
    jacquetLevel v u ≤ c₀ :=
  Nat.sInf_le h


theorem upperUnipotent3_mul_mem_bigCell3_iff (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    upperUnipotent3 x y z * g ∈ bigCell3 v ↔ g ∈ bigCell3 v := by
  simp only [bigCell3, Set.mem_setOf_eq, cornerEntry_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul]

theorem diagonal3_mul_mem_bigCell3_iff (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    diagonal3 v a * g ∈ bigCell3 v ↔ g ∈ bigCell3 v := by
  simp only [bigCell3, Set.mem_setOf_eq, cornerEntry_diagonal3_mul, lowerMinor_diagonal3_mul, ne_eq,
    mul_eq_zero, Units.ne_zero, false_or]

theorem mem_bigCell3_iff (g : LocalGL3 v) : g ∈ bigCell3 v ↔ cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0 :=
  Iff.rfl

theorem cellCutoff_subset_bigCell3 : cellCutoff v ⊆ bigCell3 v := by
  intro g h
  simp only [cellCutoff, Set.mem_setOf_eq] at h
  exact (mem_bigCell3_iff v g).mpr ⟨h.1, h.2.1⟩


theorem cellSectionOf_apply_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {g : LocalGL3 v} (hg : g ∈ bigCell3 v) :
    cellSectionOf v χ Φ g = cellValue v χ g * Φ (cellRatio v g) :=
  Set.indicator_of_mem hg _

theorem cellSectionOf_apply_of_notMem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {g : LocalGL3 v} (hg : g ∉ bigCell3 v) :
    cellSectionOf v χ Φ g = 0 :=
  Set.indicator_of_notMem hg _

theorem cellSectionOf_upperUnipotent3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    cellSectionOf v χ Φ (upperUnipotent3 x y z * g) = cellSectionOf v χ Φ g := by
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ ((upperUnipotent3_mul_mem_bigCell3_iff v x y z g).mpr hg),
      cellSectionOf_apply_of_mem v χ Φ hg, cellValue_upperUnipotent3_mul, cellRatio_upperUnipotent3_mul]
  · rw [cellSectionOf_apply_of_notMem v χ Φ (fun h => hg ((upperUnipotent3_mul_mem_bigCell3_iff v x y z g).mp h)),
      cellSectionOf_apply_of_notMem v χ Φ hg]

theorem cellSectionOf_diagonal3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    cellSectionOf v χ Φ (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * cellSectionOf v χ Φ g := by
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ ((diagonal3_mul_mem_bigCell3_iff v a g).mpr hg),
      cellSectionOf_apply_of_mem v χ Φ hg, cellValue_diagonal3_mul, cellRatio_diagonal3_mul]
    ring
  · rw [cellSectionOf_apply_of_notMem v χ Φ (fun h => hg ((diagonal3_mul_mem_bigCell3_iff v a g).mp h)),
      cellSectionOf_apply_of_notMem v χ Φ hg, mul_zero]

theorem cellSectionOf_indicator_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    cellSectionOf v χ (Set.indicator {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i) ≤ 1} 1) =
      cellSection v χ := by
  funext g
  by_cases hg : g ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ _ hg]
    by_cases hr : ∀ i, Valued.v (cellRatio v g i) ≤ 1
    · have hc : g ∈ cellCutoff v := by
        have hg' := (mem_bigCell3_iff v g).mp hg
        simp only [cellCutoff, Set.mem_setOf_eq]
        exact ⟨hg'.1, hg'.2, hr⟩
      rw [cellSection, Set.indicator_of_mem hc,
        Set.indicator_of_mem (show cellRatio v g ∈ {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i) ≤ 1}
          from hr), Pi.one_apply, mul_one]
    · have hc : g ∉ cellCutoff v := fun h => hr (by simp only [cellCutoff, Set.mem_setOf_eq] at h; exact h.2.2)
      rw [cellSection, Set.indicator_of_notMem hc,
        Set.indicator_of_notMem (show cellRatio v g ∉ {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i) ≤ 1}
          from hr), mul_zero]
  · have hc : g ∉ cellCutoff v := fun h => hg (cellCutoff_subset_bigCell3 v h)
    rw [cellSectionOf_apply_of_notMem v χ _ hg, cellSection, Set.indicator_of_notMem hc]


theorem jacquetWhittaker3_apply (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) :
    jacquetWhittaker3 v χ Φ g = jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ)) :=
  rfl

end Jacquet

end LanglandsTunnell.CubicInduction

end
