import Lemma.Random.All_MeasurableGet.is.All_MeasurableGetSlice
import Lemma.Random.All_SinglePSpace_Joint.of.All_SinglePSpace_GetSlice
import Notation.Probability.JointRv
import Notation.Fun
import Syntax.Probability.Probability
import Mathlib.MeasureTheory.Constructions.Pi
open MeasureTheory ProbabilityTheory Random Fun
open scoped ProbabilityTheory


/--
The length-1 prefix density agrees with the density of the initial state,
almost surely, by the measure-preserving identification `Fin 1 → 𝒮 ≃ 𝒮`.

| attributes | lemma |
| :---: | :---: |
| path | Random.Prob_GetSlice.ae.Prob.of.All_SinglePSpace_GetSlice.All_MeasurableGet |
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮)) :
-- imply
  have : Measurable s[:1] := All_MeasurableGetSlice.of.All_MeasurableGet hs 1
  have : SinglePSpace π (s[:1] : Ω → Fin 1 → 𝒮) := hP 1
  have : SinglePSpace π s[0] :=
    SinglePSpace.of.SinglePSpace.fst (All_SinglePSpace_Joint.of.All_SinglePSpace_GetSlice hP 0)
  ℙ[π](s[:1]) =ᵐ[π] ℙ[π](s[0]) := by
-- proof
  intro _ hP1 hP0
  let e := MeasurableEquiv.funUnique (Fin 1) 𝒮
  have href :
    ReferenceMeasure.measure (α := Fin 1 → 𝒮) =
      Measure.pi fun _ : Fin 1 => ReferenceMeasure.measure (α := 𝒮) :=
    rfl
  have hmp :
    MeasurePreserving e
      (ReferenceMeasure.measure : Measure (Fin 1 → 𝒮))
      (ReferenceMeasure.measure : Measure 𝒮) := by
    rw [href]
    apply measurePreserving_funUnique
      (ReferenceMeasure.measure : Measure 𝒮) (Fin 1)
  have hfun : s[0] = e ∘ (s[:1] : Ω → Fin 1 → 𝒮) := by
    funext ω
    simp [Fun.getSlice, Function.getSlice, FunSlice.slice, Int.toNat_zero]
    rfl
  have hmap :
    π.map s[0] =
      (π.map (s[:1] : Ω → Fin 1 → 𝒮)).map e := by
    rw [hfun]
    apply Eq.symm
    apply AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable
      hP1.aemeasurable
  have habs :
    π.map (s[:1] : Ω → Fin 1 → 𝒮) ≪
      ReferenceMeasure.measure (α := Fin 1 → 𝒮) := by
    obtain ⟨ρ, _, hlaw⟩ := hP1.exists_distribution
    rw [hlaw]
    apply withDensity_absolutelyContinuous
  have hrd :=
    e.measurableEmbedding.rnDeriv_map
      (π.map (s[:1] : Ω → Fin 1 → 𝒮))
      (ReferenceMeasure.measure (α := Fin 1 → 𝒮))
  have hrd' :
    (fun p =>
      (π.map s[0]).rnDeriv ReferenceMeasure.measure (e p)) =ᵐ[ReferenceMeasure.measure (α := Fin 1 → 𝒮)]
      fun p =>
        (π.map (s[:1] : Ω → Fin 1 → 𝒮)).rnDeriv
          ReferenceMeasure.measure p := by
    simpa [hmap, hmp.map_eq] using hrd
  have h1 := ae_of_ae_map hP1.aemeasurable (habs.ae_le hrd')
  filter_upwards [h1] with ω h
  change
    (π.map (s[:1] : Ω → Fin 1 → 𝒮)).rnDeriv ReferenceMeasure.measure
      ((s[:1] : Ω → Fin 1 → 𝒮) ω) =
    (π.map s[0]).rnDeriv ReferenceMeasure.measure (s[0] ω)
  rw [hfun, Function.comp_apply]
  apply h.symm


-- created on 2026-11-19
