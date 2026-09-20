import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| main | Random.PSpace_JointJoint.is.PSpace_Joint_Joint |
| comm | Random.PSpace_Joint_Joint.is.PSpace_JointJoint |
| mp | Random.PSpace_Joint_Joint.of.PSpace_JointJoint |
| mpr | Random.PSpace_JointJoint.of.PSpace_Joint_Joint |
-/
@[main, comm, mp, mpr]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ} :
-- imply
  PSpace π ((x, y), z) ↔ PSpace π (x, (y, z)) := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let ξ : Measure γ := ReferenceMeasure.measure
  let e : (α × β) × γ ≃ᵐ α × (β × γ) := MeasurableEquiv.prodAssoc
  have hassoc : Measure.map e ((μ.prod ν).prod ξ) = μ.prod (ν.prod ξ) := by
    simpa [e] using Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := ξ)
  have hassoc_symm : Measure.map e.symm (μ.prod (ν.prod ξ)) = (μ.prod ν).prod ξ := by
    rw [← hassoc, Measure.map_map e.symm.measurable e.measurable]
    have hcomp : (⇑e.symm ∘ ⇑e : (α × β) × γ → (α × β) × γ) = id :=
      funext fun t => e.symm_apply_apply t
    rw [hcomp, Measure.map_id]
  constructor
  ·
    intro hP
    obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
    let p' : α × (β × γ) → ENNReal := p ∘ e.symm
    have hp' : Measurable p' := (D.measurable_density).comp e.symm.measurable
    have hmap : π.map (x, (y, z)) = Measure.map e (π.map ((x, y), z)) :=
      (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable
        hP.aemeasurable).symm
    have hwd : Measure.map e (((μ.prod ν).prod ξ).withDensity p) =
        (Measure.map e ((μ.prod ν).prod ξ)).withDensity p' := by
      ext s hs
      simp only [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
        withDensity_apply _ hs, setLIntegral_map hs hp' e.measurable]
      congr
    have hlaw : π.map (x, (y, z)) = (μ.prod (ν.prod ξ)).withDensity p' := by
      rw [hmap, hjoint]
      show Measure.map e (((μ.prod ν).prod ξ).withDensity p) =
        (μ.prod (ν.prod ξ)).withDensity p'
      rw [hwd, hassoc]
    exact {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := e.measurable.comp_aemeasurable hP.aemeasurable
      exists_distribution := ⟨p', ⟨hp'⟩, hlaw⟩
    }
  ·
    intro hP
    obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
    let p' : (α × β) × γ → ENNReal := p ∘ e
    have hp' : Measurable p' := (D.measurable_density).comp e.measurable
    have hmap : π.map ((x, y), z) = Measure.map e.symm (π.map (x, (y, z))) :=
      (AEMeasurable.map_map_of_aemeasurable e.symm.measurable.aemeasurable
        hP.aemeasurable).symm
    have hwd : Measure.map e.symm ((μ.prod (ν.prod ξ)).withDensity p) =
        (Measure.map e.symm (μ.prod (ν.prod ξ))).withDensity p' := by
      ext s hs
      simp only [Measure.map_apply e.symm.measurable hs, withDensity_apply _ (e.symm.measurable hs),
        withDensity_apply _ hs, setLIntegral_map hs hp' e.symm.measurable]
      congr
    have hlaw : π.map ((x, y), z) = ((μ.prod ν).prod ξ).withDensity p' := by
      rw [hmap, hjoint]
      show Measure.map e.symm ((μ.prod (ν.prod ξ)).withDensity p) =
        ((μ.prod ν).prod ξ).withDensity p'
      rw [hwd, hassoc_symm]
    exact {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := e.symm.measurable.comp_aemeasurable hP.aemeasurable
      exists_distribution := ⟨p', ⟨hp'⟩, hlaw⟩
    }


-- created on 2026-09-19
-- updated on 2026-09-19
