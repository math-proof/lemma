import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| main | Random.PSpace.PSpace.of.PSpace_Joint |
| And.left | Random.PSpace.of.PSpace_Joint.fst |
| And.right | Random.PSpace.of.PSpace_Joint.snd |
-/
@[main, And.left, And.right]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  PSpace π x ∧ PSpace π y := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  have hx : PSpace π x := by
    let q : α → ENNReal := fun «x.bvar» ↦ lintegral ν (fun «y.bvar» ↦ p («x.bvar», «y.bvar»))
    have hq : Measurable q := hp.lintegral_prod_right'
    have hmap : π.map x =
        (π.map (x, y)).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        hP.aemeasurable).symm
    have hlaw : π.map x = μ.withDensity q := by
      have hjoint : π.map (x, y) = (μ.prod ν).withDensity p := hjoint
      rw [hmap, hjoint]
      have hmarg :
          μ.withDensity (fun «x.bvar» ↦ lintegral ν (fun «y.bvar» ↦ p («x.bvar», «y.bvar»))) =
            ((μ.prod ν).withDensity p).fst := by
        ext s hs
        rw [withDensity_apply _ hs]
        have h : ((μ.prod ν).withDensity p).fst s =
            lintegral (μ.restrict s) (fun «x.bvar» ↦ lintegral ν (fun «y.bvar» ↦ p («x.bvar», «y.bvar»))) := by
          rw [Measure.fst_apply hs, ← Set.prod_univ,
            withDensity_apply _ (MeasurableSet.prod hs MeasurableSet.univ),
            setLIntegral_prod p (hp.aemeasurable.restrict)]
          simp only [setLIntegral_univ]
        exact h.symm
      exact hmarg.symm
    exact { toIsProbabilityMeasure := inferInstance, aemeasurable := AEMeasurable.fst hP.aemeasurable, exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩ }
  have hy : PSpace π y := by
    let q : β → ENNReal := fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))
    have hq : Measurable q := hp.lintegral_prod_left'
    have hmap : π.map y =
        (π.map (x, y)).map Prod.snd :=
      (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        hP.aemeasurable).symm
    have hlaw : π.map y = ν.withDensity q := by
      have hjoint : π.map (x, y) = (μ.prod ν).withDensity p := hjoint
      rw [hmap, hjoint]
      have hmarg :
          ν.withDensity (fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))) =
            ((μ.prod ν).withDensity p).snd := by
        ext s hs
        rw [withDensity_apply _ hs]
        have h : ((μ.prod ν).withDensity p).snd s =
            lintegral (ν.restrict s) (fun «y.bvar» ↦ lintegral μ (fun «x.bvar» ↦ p («x.bvar», «y.bvar»))) := by
          rw [Measure.snd_apply hs, ← Set.univ_prod,
            withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ hs),
            setLIntegral_prod_symm p (hp.aemeasurable.restrict)]
          simp only [setLIntegral_univ]
        exact h.symm
      exact hmarg.symm
    exact { toIsProbabilityMeasure := inferInstance, aemeasurable := AEMeasurable.snd hP.aemeasurable, exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩ }
  exact ⟨hx, hy⟩


-- created on 2026-09-14
