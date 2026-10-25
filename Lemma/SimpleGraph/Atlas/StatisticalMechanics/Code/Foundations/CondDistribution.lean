import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace StatMech


/--
[regularCondDistrib_comp_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma regularCondDistrib_comp_trim_eq
  [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]
-- given
  (hm : m ≤ mΩ) :
-- imply
  (regularCondDistrib (mΩ := mΩ) μ m) ∘ₘ μ.trim hm = μ := by
-- proof
  apply StatMech.regularCondDistrib_comp_trim hm

/--
[regularCondDistrib_compProd_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma regularCondDistrib_compProd_trim_eq
  [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]
-- given
  (hm : m ≤ mΩ) :
-- imply
  (μ.trim hm) ⊗ₘ (regularCondDistrib (mΩ := mΩ) μ m) = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ := by
-- proof
  apply StatMech.regularCondDistrib_compProd_trim hm

/--
[condExp_ae_eq_integral_regularCondDistrib](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma condExp_ae_eq_integral_regularCondDistrib_eq
  [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  {f : Ω → ℝ}
-- given
  (hm : m ≤ mΩ)
  (hf : Integrable f μ) :
-- imply
  μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(regularCondDistrib (mΩ := mΩ) μ m) ω := by
-- proof
  apply StatMech.condExp_ae_eq_integral_regularCondDistrib hm hf

/--
[regularCondDistrib_ae_eq_condExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma regularCondDistrib_ae_eq_condExp_eq
  [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  {s : Set Ω}
-- given
  (hm : m ≤ mΩ)
  (hs : @MeasurableSet Ω mΩ s) :
-- imply
  (fun ω ↦ ((regularCondDistrib (mΩ := mΩ) μ m) ω).real s) =ᵐ[μ] μ⟦s := by
-- proof
  apply StatMech.regularCondDistrib_ae_eq_condExp hm hs

/--
[condDistribGiven_disintegrate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma condDistribGiven_disintegrate_eq
  [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  [Nonempty Ω] :
-- imply
  (μ.map X) ⊗ₘ condDistribGiven μ X = μ.map fun a ↦ (X a, a) := by
-- proof
  apply StatMech.condDistribGiven_disintegrate

/--
[condDistribGiven_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma condDistribGiven_comp_eq
  [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  [Nonempty Ω]
-- given
  (hX : AEMeasurable X μ) :
-- imply
  condDistribGiven μ X ∘ₘ (μ.map X) = μ := by
-- proof
  apply StatMech.condDistribGiven_comp hX

/--
[condDistribGiven_ae_eq_condExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma condDistribGiven_ae_eq_condExp_eq
  [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  [Nonempty Ω]
  {s : Set Ω}
-- given
  (hX : Measurable X)
  (hs : MeasurableSet s) :
-- imply
  (fun a ↦ (condDistribGiven μ X (X a)).real s) =ᵐ[μ] μ⟦s := by
-- proof
  apply StatMech.condDistribGiven_ae_eq_condExp hX hs

/--
[outsideSigma_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma outsideSigma_le_eq
  [Countable E]
  {Λ : Set E} :
-- imply
  outsideSigma Λ ≤ (inferInstance : MeasurableSpace (ConfigSpace E)) := by
-- proof
  apply StatMech.outsideSigma_le Λ

/--
[gibbsConditional_comp_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma gibbsConditional_comp_trim_eq
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {Λ : Set E} :
-- imply
  gibbsConditional μ Λ ∘ₘ μ.trim (outsideSigma_le Λ) = μ := by
-- proof
  apply StatMech.gibbsConditional_comp_trim μ Λ

/--
[gibbsConditional_compProd_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma gibbsConditional_compProd_trim_eq
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {Λ : Set E} :
-- imply
  (μ.trim (outsideSigma_le Λ)) ⊗ₘ (gibbsConditional μ Λ) = @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _ ((outsideSigma Λ).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ := by
-- proof
  apply StatMech.gibbsConditional_compProd_trim μ Λ

/--
[gibbsConditional_ae_eq_condExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean)
-/
@[path]
private lemma gibbsConditional_ae_eq_condExp_eq
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {Λ : Set E}
  {s : Set (ConfigSpace E)}
-- given
  (hs : MeasurableSet s) :
-- imply
  (fun ω ↦ ((gibbsConditional μ Λ) ω).real s) =ᵐ[μ] μ⟦s := by
-- proof
  apply StatMech.gibbsConditional_ae_eq_condExp μ Λ hs


-- created on 2026-10-23
