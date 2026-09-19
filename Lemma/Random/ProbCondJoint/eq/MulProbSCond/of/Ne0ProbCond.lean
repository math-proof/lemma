import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
open Random MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hP : PSpace 𝕡 (x, y, z)) :
-- imply
  have _hPxy_z : PSpace 𝕡 ((x, y), z) := PSpace_JointJoint.of.PSpace_Joint_Joint hP
  have _hPyz : PSpace 𝕡 (y, z) := PSpace.of.PSpace_Joint.snd hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
    ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
      ∀ᵐ «z.bvar» ∂ReferenceMeasure.measure,
        𝕡.condProb ((x, y), z) ((«x.bvar», «y.bvar»), «z.bvar») =
          𝕡.condProb (x, (y, z)) («x.bvar», («y.bvar», «z.bvar»)) *
            𝕡.condProb (y, z) («y.bvar», «z.bvar») := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let ξ : Measure γ := ReferenceMeasure.measure
  let e : (α × β) × γ ≃ᵐ α × (β × γ) := MeasurableEquiv.prodAssoc
  have hP_left : PSpace 𝕡 ((x, y), z) := PSpace_JointJoint.of.PSpace_Joint_Joint hP
  have hPyz : PSpace 𝕡 (y, z) := PSpace.of.PSpace_Joint.snd hP
  have hPz : PSpace 𝕡 z := PSpace.of.PSpace_Joint.snd hP_left
  let xyz : Ω → α × (β × γ) := (x, (y, z))
  let p3 : (α × β) × γ → ENNReal := 𝕡.prob ((x, y), z)
  let p3' : α × (β × γ) → ENNReal := 𝕡.prob xyz
  let p2 : β × γ → ENNReal := 𝕡.prob (y, z)
  let pz : γ → ENNReal := 𝕡.prob z
  -- The marginal density of (y, z) is finite almost everywhere
  have hlaw2m : 𝕡.map (y, z) = (ν.prod ξ).withDensity p2 :=
    PSpace.map_eq_withDensity_density
  have hi2 : IsProbabilityMeasure (𝕡.map (y, z)) :=
    Measure.isProbabilityMeasure_map hPyz.aemeasurable
  have htot2 : ∫⁻ bc, p2 bc ∂(ν.prod ξ) = 1 := by
    have h : (ν.prod ξ).withDensity p2 Set.univ = ∫⁻ bc, p2 bc ∂(ν.prod ξ) := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [← hlaw2m, measure_univ] at h
    exact h.symm
  have hmp2 : Measurable p2 := Measure.measurable_rnDeriv _ _
  have hfin2 : ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, p2 (b, c) < ⊤ :=
    Measure.ae_ae_of_ae_prod (ae_lt_top hmp2 (by rw [htot2]; norm_num))
  -- Joint density factorisation against the (y, z) marginal: p3' = p(x|y,z) * p2
  have hI := All_Eq_MulProbCond.of.PSpace_Joint hP
  have hI3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ,
      p3' (a, (b, c)) =
        𝕡.condProb xyz (a, (b, c)) * p2 (b, c) := by
    filter_upwards [hI] with a ha
    exact Measure.ae_ae_of_ae_prod ha
  -- The two associations of the triple density agree a.e. (rnDeriv transported by prodAssoc)
  have hmap : 𝕡.map xyz = Measure.map e (𝕡.map ((x, y), z)) :=
    (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable
      hP_left.aemeasurable).symm
  have hρ : Measure.map e ((μ.prod ν).prod ξ) = μ.prod (ν.prod ξ) :=
    Measure.prodAssoc_prod
  have hrn :=
    (MeasurableEquiv.measurableEmbedding e).rnDeriv_map
      (𝕡.map ((x, y), z)) ((μ.prod ν).prod ξ)
  have htrans' :
      (fun t : (α × β) × γ ↦ p3' (e t)) =ᵐ[(μ.prod ν).prod ξ] p3 := by
    simp only [← hmap, hρ] at hrn
    show (fun t ↦ (𝕡.map xyz).rnDeriv (μ.prod (ν.prod ξ)) (e t)) =ᵐ[(μ.prod ν).prod ξ]
      (𝕡.map ((x, y), z)).rnDeriv ((μ.prod ν).prod ξ)
    exact hrn
  have htrans : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ,
      p3 ((a, b), c) = p3' (a, (b, c)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod htrans')] with a ha
    filter_upwards [ha] with b hb
    filter_upwards [hb] with c hc
    have hec : e ((a, b), c) = (a, (b, c)) := rfl
    rw [hec] at hc
    exact hc.symm
  have hfin3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, p2 (b, c) < ⊤ := by
    filter_upwards with a
    exact hfin2
  -- Denominator maps in the condProb definitions
  have hdenz : 𝕡.map (fun ω ↦ (((x, y), z) ω).2) = 𝕡.map z := by congr
  have hden2 : 𝕡.map (fun ω ↦ ((y, z) ω).2) = 𝕡.map z := by congr
  have hdenyz : 𝕡.map (fun ω ↦ (xyz ω).2) = 𝕡.map (y, z) := by congr
  filter_upwards [htrans, hI3, hfin3] with a htr hI hlt
  filter_upwards [htr, hI, hlt] with b htr hI hlt
  filter_upwards [htr, hI, hlt] with c htr hI hlt
  have h0 : p2 (b, c) = 0 → p3' (a, (b, c)) = 0 := by
    intro h; rw [hI, h, mul_zero]
  have hcan : (p3' (a, (b, c)) / p2 (b, c)) * p2 (b, c) = p3' (a, (b, c)) :=
    ENNReal.div_mul_cancel' h0 (fun h ↦ (hlt.ne h).elim)
  have hA : 𝕡.condProb ((x, y), z) ((a, b), c) = p3 ((a, b), c) / pz c := by
    unfold Measure.condProb Measure.prob
    rw [hdenz]; rfl
  have hB : 𝕡.condProb (y, z) (b, c) = p2 (b, c) / pz c := by
    unfold Measure.condProb Measure.prob
    rw [hden2]; rfl
  have hC : 𝕡.condProb xyz (a, (b, c)) = p3' (a, (b, c)) / p2 (b, c) := by
    unfold Measure.condProb Measure.prob
    rw [hdenyz]; rfl
  rw [hA, hB, hC, htr]
  symm
  calc
    _ = ((p3' (a, (b, c)) / p2 (b, c)) * p2 (b, c)) / pz c := by
        simp only [div_eq_mul_inv]; ac_rfl
    _ = p3' (a, (b, c)) / pz c := by rw [hcan]


-- created on 2026-09-19
