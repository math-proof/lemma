import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasurableSpace Set MeasureTheory MeasureTheory.SimpleFunc
open scoped ENNReal NNReal


namespace MeasurabilityOfFunctions

/--
[measurable_generateFrom_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasurabilityOfFunctions.lean)
-/
@[path]
lemma measurable_generateFrom_iff
  [MeasurableSpace X]
  {G : Set (Set Y)}
  {f : X → Y} :
-- imply
  @Measurable X Y _ (generateFrom G) f ↔ ∀ A ∈ G, MeasurableSet (f ⁻¹' A) := by
-- proof
  constructor
  · intro hf A hA
    exact hf (measurableSet_generateFrom hA)
  · exact measurable_generateFrom

end MeasurabilityOfFunctions

namespace MeasurabilityOfFunctions

/--
[continuous_imp_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasurabilityOfFunctions.lean)
-/
@[path]
lemma continuous_imp_measurable
  [MetricSpace X]
  [MetricSpace Y]
  [MeasurableSpace X]
  [BorelSpace X]
  [MeasurableSpace Y]
  [BorelSpace Y]
  {f : X → Y}
-- given
  (hf : Continuous f) :
-- imply
  Measurable f :=
-- proof
  hf.measurable

end MeasurabilityOfFunctions

/--
[ennrealRatEmbed_dense_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasurabilityOfFunctions.lean)
-/
@[path]
lemma ennrealRatEmbed_dense_Icc
-- given
  (C : ENNReal)
  (hC : C ≠ ⊤)
  (ε : ENNReal)
  (hε : 0 < ε) :
-- imply
  ∃ N : ℕ, ∀ v : ENNReal, v ≤ C → ∃ k : ℕ, k < N ∧ ennrealRatEmbed k ≤ v ∧ v - ennrealRatEmbed k < ε := by
-- proof
  obtain ⟨q, hq0, hq_pos_ennreal, hqε⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hε
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    by_contra h
    simp only [not_lt] at h
    have h1 : Real.toNNReal (q : ℝ) = 0 := Real.toNNReal_eq_zero.mpr h
    simp [h1] at hq_pos_ennreal
  set δ : ℝ := (q : ℝ) with hδ_def
  set M : ℕ := ⌊C.toReal / δ⌋₊
  let encodeFn : ℕ → ℕ := fun j => Encodable.encode ((j : ℚ) * q)
  use 1 + (Finset.range (M + 1)).sup encodeFn
  intro v hv
  have hv_ne : v ≠ ⊤ := ne_top_of_le_ne_top hC hv
  have hv_le_r : v.toReal ≤ C.toReal := (ENNReal.toReal_le_toReal hv_ne hC).mpr hv
  set i : ℕ := ⌊v.toReal / δ⌋₊
  have hi_le : i ≤ M := Nat.floor_le_floor (div_le_div_of_nonneg_right hv_le_r hq_pos.le)
  have hi_mem : i ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have key : ennrealRatEmbed (Encodable.encode ((↑i : ℚ) * q)) =
    ENNReal.ofReal ((i : ℝ) * δ) := by
    have h1 := ennrealRatEmbed_encode ((↑i : ℚ) * q)
    rw [h1]
    unfold ENNReal.ofReal
    congr 1
    congr 1
    rw [hδ_def]
    push_cast
    ring
  have hiδ_le : (i : ℝ) * δ ≤ v.toReal := by
    have h1 : (↑i : ℝ) ≤ v.toReal / δ :=
      Nat.floor_le (div_nonneg ENNReal.toReal_nonneg hq_pos.le)
    have h2 : v.toReal / δ * δ = v.toReal := div_mul_cancel₀ v.toReal hq_pos.ne'
    calc (↑i : ℝ) * δ ≤ v.toReal / δ * δ :=
      mul_le_mul_of_nonneg_right h1 hq_pos.le
      _ = v.toReal := h2
  have hv_lt : v.toReal < ((↑i : ℝ) + 1) * δ := by
    have h1 := Nat.lt_floor_add_one (v.toReal / δ)
    have h2 : v.toReal / δ * δ = v.toReal := div_mul_cancel₀ v.toReal hq_pos.ne'
    calc v.toReal = v.toReal / δ * δ := h2.symm
      _ < ((↑i : ℝ) + 1) * δ := mul_lt_mul_of_pos_right h1 hq_pos
  have hiδ_nn : (0 : ℝ) ≤ (↑i : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hq_pos.le
  refine ⟨Encodable.encode ((i : ℚ) * q), ?_, ?_, ?_⟩
  · have hsup := Finset.le_sup (f := encodeFn) hi_mem
    change encodeFn i < _
    omega
  · rw [key, ← ENNReal.ofReal_toReal hv_ne]
    exact ENNReal.ofReal_le_ofReal hiδ_le
  · rw [key]
    have hvsub : v.toReal - (↑i : ℝ) * δ < δ := by nlinarith
    calc v - ENNReal.ofReal ((↑i : ℝ) * δ)
      = ENNReal.ofReal v.toReal - ENNReal.ofReal ((↑i : ℝ) * δ) := by
        rw [ENNReal.ofReal_toReal hv_ne]
      _ = ENNReal.ofReal (v.toReal - (↑i : ℝ) * δ) := (ENNReal.ofReal_sub v.toReal hiδ_nn).symm
      _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hq_pos]; exact hvsub
      _ = ↑(Real.toNNReal δ) := rfl
      _ < ε := hqε


-- created on 2026-10-23
