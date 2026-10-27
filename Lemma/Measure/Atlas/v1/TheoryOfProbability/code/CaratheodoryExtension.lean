import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.CaratheodoryExtension
open Set MeasureTheory MeasureTheory.Measure MeasurableSpace
open scoped ENNReal


/--
[isSetAlgebra_isPiSystem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CaratheodoryExtension.lean)
-/
@[path]
lemma isSetAlgebra_isPiSystem
  {𝒜 : Set (Set α)}
-- given
  (h : IsSetAlgebra 𝒜) :
-- imply
  IsPiSystem 𝒜 :=
-- proof
  fun _s hs _t ht _ => h.inter_mem hs ht

/--
[exists_measure_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CaratheodoryExtension.lean)
-/
@[path]
lemma exists_measure_extension
  {𝒜 : Set (Set α)}
-- given
  (h𝒜 : IsSetAlgebra 𝒜)
  (μ₀ : AddContent ℝ≥0∞ 𝒜)
  (hμ₀_sigma : μ₀.IsSigmaSubadditive) :
-- imply
  ∃ μ : @Measure α (generateFrom 𝒜), ∀ s ∈ 𝒜, μ s = μ₀ s := by
-- proof
  letI : MeasurableSpace α := generateFrom 𝒜
  have h_semi : IsSetSemiring 𝒜 := isSetSemiring_of_isSetAlgebra h𝒜
  exact ⟨μ₀.measure h_semi le_rfl hμ₀_sigma, fun s hs =>
    μ₀.measure_eq h_semi rfl hμ₀_sigma hs⟩

/--
[caratheodory_extension_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CaratheodoryExtension.lean)
-/
@[path]
lemma caratheodory_extension_theorem
  {𝒜 : Set (Set α)}
  {B : ℕ → Set α}
-- given
  (h𝒜 : IsSetAlgebra 𝒜)
  (μ₀ : AddContent ℝ≥0∞ 𝒜)
  (hμ₀_sigma : μ₀.IsSigmaSubadditive)
  (hB_mem : ∀ i, B i ∈ 𝒜)
  (hB_cover : ⋃ i, B i = univ)
  (hB_fin : ∀ i, μ₀ (B i) ≠ ⊤) :
-- imply
  ∃! μ : @Measure α (generateFrom 𝒜), ∀ s ∈ 𝒜, μ s = μ₀ s := by
-- proof
  obtain ⟨μ, hμ⟩ := exists_measure_extension 𝒜 h𝒜 μ₀ hμ₀_sigma
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  exact (ext_of_generateFrom_of_iUnion 𝒜 B rfl (isSetAlgebra_isPiSystem h𝒜) hB_cover hB_mem
    (fun i => by rw [hμ (B i) (hB_mem i)]; exact hB_fin i)
    (fun s hs => by rw [hμ s hs, hν s hs])).symm


-- created on 2026-10-23
