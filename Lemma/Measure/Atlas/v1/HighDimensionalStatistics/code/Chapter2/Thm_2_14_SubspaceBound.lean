import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_14_SubspaceBound
open Matrix Finset BigOperators Rigollet MeasureTheory


/--
[euclidean_inner_eq_dotProduct_withLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_SubspaceBound.lean)
-/
@[path]
lemma euclidean_inner_eq_dotProduct_withLp
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  @inner ℝ (EuclideanSpace ℝ (Fin n)) _ ((WithLp.equiv 2 (Fin n → ℝ)).symm x) ((WithLp.equiv 2 (Fin n → ℝ)).symm y) = dotProduct x y := by
-- proof
  simp only [inner, dotProduct]
  congr 1; ext i; simp [WithLp.equiv]; ring

/--
[column_span_onb](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_SubspaceBound.lean)
-/
@[path]
lemma column_span_onb
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {θstar : Fin d → ℝ}
  {S : Finset (Fin d)}
  {k : ℕ}
-- given
  (hSk : S.card = k)
  (hk1 : 1 ≤ k) :
-- imply
  ∃ (r : ℕ) (_ : 0 < r) (Φ : Fin r → (Fin n → ℝ)), r ≤ k + l0norm θstar ∧ (∀ a : Fin r → ℝ, dotProduct a a ≤ 1 → dotProduct (∑ j, a j • Φ j) (∑ j, a j • Φ j) ≤ 1) := by
-- proof
  set T := S ∪ Finset.univ.filter (fun j => θstar j ≠ 0)
  let toE := (WithLp.equiv 2 (Fin n → ℝ)).symm
  let fromE := (WithLp.equiv 2 (Fin n → ℝ))
  set cols := T.image (fun j => toE (fun i => X i j))
  set Vm := Submodule.span ℝ (cols : Set (EuclideanSpace ℝ (Fin n)))
  haveI : FiniteDimensional ℝ Vm := FiniteDimensional.span_finset ℝ cols
  set r' := Module.finrank ℝ Vm
  have r'_le : r' ≤ k + l0norm θstar := by
    calc r' ≤ cols.card := finrank_span_finset_le_card cols
      _ ≤ T.card := Finset.card_image_le
      _ ≤ S.card + (Finset.univ.filter (fun j => θstar j ≠ 0)).card :=
        Finset.card_union_le _ _
      _ = k + l0norm θstar := by rw [hSk]; rfl
  by_cases hr'0 : r' = 0
  ·
    exact ⟨1, Nat.one_pos, fun _ => 0, by omega,
      fun a ha => by simp [dotProduct, mul_zero, Finset.sum_const_zero]⟩
  ·
    have hr'_pos : 0 < r' := Nat.pos_of_ne_zero hr'0
    set he := stdOrthonormalBasis ℝ Vm
    set Φ : Fin r' → (Fin n → ℝ) := fun j => fromE (Vm.subtypeₗᵢ (he j))
    refine ⟨r', hr'_pos, Φ, r'_le, ?_⟩
    intro a ha
    have horth : Orthonormal ℝ (fun j => (Vm.subtypeₗᵢ (he j) : EuclideanSpace ℝ (Fin n))) :=
      he.orthonormal.comp_linearIsometry Vm.subtypeₗᵢ
    suffices h : @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (∑ j, a j • Vm.subtypeₗᵢ (he j)) (∑ j, a j • Vm.subtypeₗᵢ (he j)) ≤ 1 by
      have bridge : dotProduct (∑ j, a j • Φ j) (∑ j, a j • Φ j) =
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _
          (∑ j, a j • Vm.subtypeₗᵢ (he j))
          (∑ j, a j • Vm.subtypeₗᵢ (he j)) := by
        rw [← euclidean_inner_eq_dotProduct_withLp]
        congr 1 <;> simp [Φ, fromE]
      linarith
    calc @inner ℝ _ _ (∑ j, a j • Vm.subtypeₗᵢ (he j)) (∑ j, a j • Vm.subtypeₗᵢ (he j))
      = ∑ i, starRingEnd ℝ (a i) * a i := horth.inner_sum a a Finset.univ
      _ = dotProduct a a := by simp [dotProduct]
      _ ≤ 1 := ha

/--
[subspace_thm119_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Thm_2_14_SubspaceBound.lean)
-/
@[path]
lemma subspace_thm119_bound
  {n : ℕ}
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [IsProbabilityMeasure μ]
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {r : ℕ}
  {Φ : Fin r → (Fin n → ℝ)}
  {threshold : ℝ}
-- given
  (hσ : 0 < σ)
  (hε : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ)
  (hε_indep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
  (hε_meas : ∀ i : Fin n, Measurable (fun ω => ε ω i))
  (hr : 0 < r)
  (hΦ_orth : ∀ a : Fin r → ℝ, dotProduct a a ≤ 1 → dotProduct (∑ j, a j • Φ j) (∑ j, a j • Φ j) ≤ 1)
  (ht_pos : 0 < threshold) :
-- imply
  μ {ω : Ω | ∃ (a : Fin r → ℝ), dotProduct a a ≤ 1 ∧ dotProduct (∑ j, a j • Φ j) (ε ω) > threshold} ≤ ENNReal.ofReal ((6 : ℝ) ^ r * Real.exp (-(threshold ^ 2 / (8 * σ ^ 2)))) := by
-- proof
  set Z : Ω → Fin r → ℝ := fun ω j => dotProduct (Φ j) (ε ω) with hZ_def
  have hkey : ∀ ω a, dotProduct (∑ j : Fin r, a j • Φ j) (ε ω) = dotProduct a (Z ω) := by
    intro ω a
    simp only [hZ_def, dotProduct]
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1; ext i
    rw [Finset.mul_sum]
    congr 1; ext j; ring
  have hcontain : {ω : Ω | ∃ (a : Fin r → ℝ), dotProduct a a ≤ 1 ∧
    dotProduct (∑ j, a j • Φ j) (ε ω) > threshold} ⊆
    {ω | ∃ θ : Fin r → ℝ, dotProduct θ θ ≤ 1 ∧ dotProduct θ (Z ω) > threshold} := by
    intro ω ⟨a, ha_unit, ha_big⟩
    exact ⟨a, ha_unit, by rwa [← hkey]⟩
  have hsg : ∀ (a : Fin r → ℝ), dotProduct a a ≤ 1 →
    IsSubGaussian (fun ω => dotProduct a (Z ω)) (σ ^ 2) μ := by
    intro a ha
    have heq : (fun ω => dotProduct a (Z ω)) = fun ω => dotProduct (∑ j, a j • Φ j) (ε ω) := by
      ext ω; rw [← hkey]
    rw [heq]
    set v := ∑ j : Fin r, a j • Φ j with hv_def
    have hv_unit : dotProduct v v ≤ 1 := hΦ_orth a ha
    have heq2 : (fun ω => dotProduct v (ε ω)) =
      fun ω => @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (toEuc n v) (toEuc n (ε ω)) := by
      ext ω; rw [← dotProduct_eq_inner_euclidean]
    rw [heq2]
    exact subgaussian_inner_from_coord (sq_nonneg σ) hε hε_indep hε_meas (toEuc n v)
      ((euclidean_norm_le_one_iff v).mpr hv_unit)
  have h119 := theorem_1_19_tail_bound_vec hr (hσ := sq_pos_of_pos hσ) hsg threshold ht_pos
  calc μ _ ≤ μ {ω | ∃ θ : Fin r → ℝ, dotProduct θ θ ≤ 1 ∧ dotProduct θ (Z ω) > threshold} :=
    measure_mono hcontain
    _ ≤ ENNReal.ofReal ((6 : ℝ) ^ r * Real.exp (-(threshold ^ 2 / (8 * σ ^ 2)))) := h119
/-- Axiomatized geometric containment: the event that some `θ` supported on `S`
violates a quadratic bound is contained in an event about unit linear combinations of the
orthonormal basis `Φ`. Used as a bridge in the proof of Theorem 2.14. -/


-- created on 2026-10-23
