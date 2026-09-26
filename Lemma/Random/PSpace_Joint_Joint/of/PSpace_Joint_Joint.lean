import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import sympy.stats.joint_rv
open Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : MeasureTheory.Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hP : PSpace π (x, y, z)) :
-- imply
  PSpace π (y, x, z) := by
-- proof
  let μ : MeasureTheory.Measure α := ReferenceMeasure.measure
  let ν : MeasureTheory.Measure β := ReferenceMeasure.measure
  let ξ : MeasureTheory.Measure γ := ReferenceMeasure.measure
  have hL : PSpace π ((x, y), z) := PSpace_JointJoint.of.PSpace_Joint_Joint hP
  have hL' : PSpace π ((y, x), z) := by
    obtain ⟨p, D, hjoint⟩ := hL.exists_distribution
    let swap1 : (α × β) × γ → (β × α) × γ := Prod.map Prod.swap (id : γ → γ)
    have hswap1 : Measurable swap1 := measurable_swap.prodMap measurable_id
    let swap1' : (β × α) × γ → (α × β) × γ := Prod.map Prod.swap (id : γ → γ)
    have hswap1' : Measurable swap1' := measurable_swap.prodMap measurable_id
    let p' : (β × α) × γ → ENNReal := p ∘ swap1'
    have hp' : Measurable p' := D.measurable_density.comp hswap1'
    have hmap : π.map ((y, x), z) = MeasureTheory.Measure.map swap1 (π.map ((x, y), z)) := by
      change π.map (fun ω ↦ ((y ω, x ω), z ω)) =
        MeasureTheory.Measure.map swap1 (π.map (fun ω ↦ ((x ω, y ω), z ω)))
      have hcomp :
          (fun ω ↦ ((y ω, x ω), z ω)) =
            swap1 ∘ fun ω ↦ ((x ω, y ω), z ω) := by
        funext ω; rfl
      rw [hcomp]
      exact (AEMeasurable.map_map_of_aemeasurable hswap1.aemeasurable hL.aemeasurable).symm
    have href : MeasureTheory.Measure.map swap1 ((μ.prod ν).prod ξ) = (ν.prod μ).prod ξ := by
      simpa [MeasureTheory.Measure.prod_swap, MeasureTheory.Measure.map_id] using
        (MeasureTheory.Measure.map_prod_map (μ.prod ν) ξ measurable_swap measurable_id).symm
    have hwd :
        MeasureTheory.Measure.map swap1 (((μ.prod ν).prod ξ).withDensity p) =
          (MeasureTheory.Measure.map swap1 ((μ.prod ν).prod ξ)).withDensity p' := by
      ext s hs
      simp only [MeasureTheory.Measure.map_apply hswap1 hs, MeasureTheory.withDensity_apply _ (hswap1 hs),
        MeasureTheory.withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hp' hswap1]
      congr
    have hlaw : π.map ((y, x), z) = ((ν.prod μ).prod ξ).withDensity p' := by
      rw [hmap, hjoint]
      show MeasureTheory.Measure.map swap1 (((μ.prod ν).prod ξ).withDensity p) =
        ((ν.prod μ).prod ξ).withDensity p'
      rw [hwd, href]
    exact {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := hswap1.comp_aemeasurable hL.aemeasurable
      exists_distribution := ⟨p', ⟨hp'⟩, hlaw⟩
    }
  exact PSpace_Joint_Joint.of.PSpace_JointJoint hL'


-- created on 2026-09-23
-- updated on 2026-09-26
