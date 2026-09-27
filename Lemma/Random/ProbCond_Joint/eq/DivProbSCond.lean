import Lemma.Random.All_EqProbCondJoint
import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import Lemma.Random.PSpace_Joint
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.PSpace_Joint_Joint.of.PSpace_Joint_Joint
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
  have _hPxy_z : PSpace π ((x, y), z) := PSpace_JointJoint.of.PSpace_Joint_Joint hP
  have _hPxz : PSpace π (x, z) :=
    PSpace_Joint.comm
      (PSpace.of.PSpace_Joint.fst
        (PSpace_JointJoint.of.PSpace_Joint_Joint
          (PSpace_Joint.comm (PSpace_JointJoint.of.PSpace_Joint_Joint hP))))
  have _hPyxz : PSpace π (y, x, z) := PSpace_Joint_Joint.of.PSpace_Joint_Joint hP
  ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
      ∀ᵐ «z.bvar» ∂ReferenceMeasure.measure,
        ℙ[π](y = «y.bvar» | x = «x.bvar» ∧ z = «z.bvar») =
          ℙ[π](x = «x.bvar» ∧ y = «y.bvar» | z = «z.bvar») /
            ℙ[π](x = «x.bvar» | z = «z.bvar») := by
-- proof
  intro hPxy_z hPxz hPyxz
  let μ : MeasureTheory.Measure α := ReferenceMeasure.measure
  let ν : MeasureTheory.Measure β := ReferenceMeasure.measure
  let ξ : MeasureTheory.Measure γ := ReferenceMeasure.measure
  have hL_yx : PSpace π ((y, x), z) := PSpace_JointJoint.of.PSpace_Joint_Joint hPyxz
  have hPz : PSpace π z := PSpace.of.PSpace_Joint.snd hPxz
  have hchain :
      ∀ᵐ b ∂ReferenceMeasure.measure,
        ∀ᵐ a ∂ReferenceMeasure.measure,
          ∀ᵐ c ∂ReferenceMeasure.measure,
            π.condProb ((y, x), z) ((b, a), c) =
              π.condProb (y, (x, z)) (b, (a, c)) *
                π.condProb (x, z) (a, c) :=
    All_EqProbCondJoint hPyxz
  obtain ⟨p_xy, D_xy, hlaw_xy⟩ := hPxy_z.exists_distribution
  have hp_xy : Measurable p_xy := D_xy.measurable_density
  let swap1 : (α × β) × γ → (β × α) × γ := Prod.map Prod.swap (id : γ → γ)
  have hswap1 : Measurable swap1 := measurable_swap.prodMap measurable_id
  let swap1' : (β × α) × γ → (α × β) × γ := Prod.map Prod.swap (id : γ → γ)
  have hswap1' : Measurable swap1' := measurable_swap.prodMap measurable_id
  have hmap_swap : π.map ((y, x), z) = MeasureTheory.Measure.map swap1 (π.map ((x, y), z)) := by
    change π.map (fun ω ↦ ((y ω, x ω), z ω)) =
      MeasureTheory.Measure.map swap1 (π.map (fun ω ↦ ((x ω, y ω), z ω)))
    have hcomp :
        (fun ω ↦ ((y ω, x ω), z ω)) =
          swap1 ∘ fun ω ↦ ((x ω, y ω), z ω) := by
      funext ω; rfl
    rw [hcomp]
    exact (AEMeasurable.map_map_of_aemeasurable hswap1.aemeasurable hPxy_z.aemeasurable).symm
  have href_swap : MeasureTheory.Measure.map swap1 ((μ.prod ν).prod ξ) = (ν.prod μ).prod ξ := by
    simpa [MeasureTheory.Measure.prod_swap, MeasureTheory.Measure.map_id] using
      (MeasureTheory.Measure.map_prod_map (μ.prod ν) ξ measurable_swap measurable_id).symm
  have href_swap' : MeasureTheory.Measure.map swap1' ((ν.prod μ).prod ξ) = (μ.prod ν).prod ξ := by
    have hinv : swap1' ∘ swap1 = (id : (α × β) × γ → (α × β) × γ) := by
      funext t
      obtain ⟨⟨a, b⟩, c⟩ := t
      rfl
    calc
      _ = MeasureTheory.Measure.map swap1' (MeasureTheory.Measure.map swap1 ((μ.prod ν).prod ξ)) := by
            rw [← href_swap]
      _ = MeasureTheory.Measure.map (swap1' ∘ swap1) ((μ.prod ν).prod ξ) :=
            MeasureTheory.Measure.map_map hswap1' hswap1
      _ = MeasureTheory.Measure.map id ((μ.prod ν).prod ξ) := by rw [hinv]
      _ = (μ.prod ν).prod ξ := MeasureTheory.Measure.map_id
  have hlaw_yx :
      π.map ((y, x), z) =
        ((ν.prod μ).prod ξ).withDensity (p_xy ∘ swap1') := by
    have hp' : Measurable (p_xy ∘ swap1') := hp_xy.comp hswap1'
    rw [hmap_swap, hlaw_xy]
    show MeasureTheory.Measure.map swap1 (((μ.prod ν).prod ξ).withDensity p_xy) =
      ((ν.prod μ).prod ξ).withDensity (p_xy ∘ swap1')
    have hwd :
        MeasureTheory.Measure.map swap1 (((μ.prod ν).prod ξ).withDensity p_xy) =
          (MeasureTheory.Measure.map swap1 ((μ.prod ν).prod ξ)).withDensity (p_xy ∘ swap1') := by
      ext s hs
      simp only [MeasureTheory.Measure.map_apply hswap1 hs, MeasureTheory.withDensity_apply _ (hswap1 hs),
        MeasureTheory.withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hp' hswap1]
      congr
    rw [hwd, href_swap]
  have hprob_yx :
      π.prob ((y, x), z) =ᵐ[(ν.prod μ).prod ξ] (p_xy ∘ swap1') := by
    show (π.map ((y, x), z)).rnDeriv ((ν.prod μ).prod ξ) =ᵐ[_] _
    rw [hlaw_yx]
    exact MeasureTheory.Measure.rnDeriv_withDensity _ (hp_xy.comp hswap1')
  have hprob_xy :
      π.prob ((x, y), z) =ᵐ[(μ.prod ν).prod ξ] p_xy := by
    show (π.map ((x, y), z)).rnDeriv ((μ.prod ν).prod ξ) =ᵐ[_] _
    rw [hlaw_xy]
    exact MeasureTheory.Measure.rnDeriv_withDensity _ hp_xy
  have hMP' : MeasureTheory.MeasurePreserving swap1' ((ν.prod μ).prod ξ) ((μ.prod ν).prod ξ) :=
    ⟨hswap1', href_swap'⟩
  have hprob_xy_push :
      (fun t ↦ π.prob ((x, y), z) (swap1' t)) =ᵐ[(ν.prod μ).prod ξ]
        (p_xy ∘ swap1') :=
    hMP'.quasiMeasurePreserving.ae_eq_comp hprob_xy
  have hden_yx : π.map (fun ω ↦ (((y, x), z) ω).2) = π.map z := by congr
  have hden_xy : π.map (fun ω ↦ (((x, y), z) ω).2) = π.map z := by congr
  have hjoint_eq :
      (fun t ↦ π.condProb ((y, x), z) t) =ᵐ[(ν.prod μ).prod ξ]
        fun t ↦ π.condProb ((x, y), z) (swap1' t) := by
    filter_upwards [hprob_yx, hprob_xy_push] with t hyx hxy
    unfold MeasureTheory.Measure.condProb
    rw [hden_yx, hden_xy, hyx, hxy]
    -- swap1' preserves the second coordinate
    rfl

  have hjoint' :
      ∀ᵐ b ∂ReferenceMeasure.measure,
        ∀ᵐ a ∂ReferenceMeasure.measure,
          ∀ᵐ c ∂ReferenceMeasure.measure,
            π.condProb ((y, x), z) ((b, a), c) =
              π.condProb ((x, y), z) (swap1' ((b, a), c)) := by
    simpa [μ, ν, ξ] using
      MeasureTheory.Measure.ae_ae_of_ae_prod (MeasureTheory.Measure.ae_ae_of_ae_prod hjoint_eq)
  let p2 : α × γ → ENNReal := π.prob (x, z)
  let pz : γ → ENNReal := π.prob z
  have hlaw2m : π.map (x, z) = (μ.prod ξ).withDensity p2 :=
    PSpace.map_eq_withDensity_density
  have htot2 : ∫⁻ ac, p2 ac ∂(μ.prod ξ) = 1 := by
    have h : (μ.prod ξ).withDensity p2 Set.univ = ∫⁻ ac, p2 ac ∂(μ.prod ξ) := by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ]
    have : MeasureTheory.IsProbabilityMeasure (π.map (x, z)) :=
      MeasureTheory.Measure.isProbabilityMeasure_map hPxz.aemeasurable
    rw [← hlaw2m, MeasureTheory.measure_univ] at h
    exact h.symm
  have hmp2 : Measurable p2 := by
    simpa [p2, MeasureTheory.Measure.prob] using MeasureTheory.Measure.measurable_rnDeriv (π.map (x, z)) ReferenceMeasure.measure
  have hfin2 : ∀ᵐ a ∂ReferenceMeasure.measure, ∀ᵐ c ∂ReferenceMeasure.measure, p2 (a, c) < ⊤ :=
    MeasureTheory.Measure.ae_ae_of_ae_prod (MeasureTheory.ae_lt_top hmp2 (by rw [htot2]; norm_num))
  have hmp_z : Measurable pz := by
    simpa [pz, MeasureTheory.Measure.prob] using MeasureTheory.Measure.measurable_rnDeriv (π.map z) ReferenceMeasure.measure
  have hlaw_z : π.map z = ξ.withDensity pz := PSpace.map_eq_withDensity_density
  have htot_z : ∫⁻ c, pz c ∂ξ = 1 := by
    have h : ξ.withDensity pz Set.univ = ∫⁻ c, pz c ∂ξ := by
      rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ]
    have : MeasureTheory.IsProbabilityMeasure (π.map z) :=
      MeasureTheory.Measure.isProbabilityMeasure_map hPz.aemeasurable
    rw [← h, ← hlaw_z, MeasureTheory.measure_univ]
  have hfin_z : ∀ᵐ c ∂ReferenceMeasure.measure, pz c < ⊤ :=
    MeasureTheory.ae_lt_top hmp_z (by rw [htot_z]; norm_num)
  have hmul_yxz0 := All_Eq_MulProbCond.of.PSpace_Joint (x := y) (y := (x, z)) hPyxz
  have hmul_yxz : ∀ᵐ b ∂ReferenceMeasure.measure, ∀ᵐ a ∂ReferenceMeasure.measure, ∀ᵐ c ∂ReferenceMeasure.measure,
      π.prob (y, (x, z)) (b, (a, c)) =
        π.condProb (y, (x, z)) (b, (a, c)) * p2 (a, c) := by
    filter_upwards [hmul_yxz0] with b hb
    have hb' := MeasureTheory.Measure.ae_ae_of_ae_prod hb
    filter_upwards [hb'] with a ha
    filter_upwards [ha] with c hc
    simpa [p2] using hc
  have hmul_xz0 := All_Eq_MulProbCond.of.PSpace_Joint hPxz
  have hmul_xz : ∀ᵐ a ∂ReferenceMeasure.measure, ∀ᵐ c ∂ReferenceMeasure.measure,
      π.condProb (x, z) (a, c) * pz c = p2 (a, c) := by
    filter_upwards [hmul_xz0] with a ha
    filter_upwards [ha] with c hc
    refine Eq.symm ?_
    simpa [p2, pz] using hc
  filter_upwards [hchain.and (hjoint'.and hmul_yxz)] with b hb
  have hb_ch := hb.1
  have hb_j := hb.2.1
  have hb_my := hb.2.2
  filter_upwards [hb_ch.and (hb_j.and hb_my), hfin2.and hmul_xz] with a ha hax
  have ha_ch := ha.1
  have ha_j := ha.2.1
  have ha_my := ha.2.2
  have ha_fin := hax.1
  have ha_mx := hax.2
  filter_upwards [ha_ch.and (ha_j.and (ha_my.and (ha_fin.and ha_mx))), hfin_z] with c hc hc_fz
  have hc_ch := hc.1
  have hc_j := hc.2.1
  have hc_my := hc.2.2.1
  have hc_fin := hc.2.2.2.1
  have hc_mx := hc.2.2.2.2
  have hswap_pt : swap1' ((b, a), c) = ((a, b), c) := rfl
  have hjoint_pt :
      π.condProb ((y, x), z) ((b, a), c) =
        π.condProb ((x, y), z) ((a, b), c) := by
    simpa [hswap_pt] using hc_j
  have hmul_pt :
      π.condProb ((x, y), z) ((a, b), c) =
        π.condProb (y, (x, z)) (b, (a, c)) *
          π.condProb (x, z) (a, c) := by
    rw [← hjoint_pt, hc_ch]
  change π.condProb (y, (x, z)) (b, (a, c)) =
    π.condProb ((x, y), z) ((a, b), c) / π.condProb (x, z) (a, c)
  rw [hmul_pt]
  refine (ENNReal.mul_div_cancel_right' ?_ ?_).symm
  · intro h0
    have hdenyz : π.map (fun ω ↦ ((y, (x, z)) ω).2) = π.map (x, z) := by congr
    have hC : π.condProb (y, (x, z)) (b, (a, c)) =
        π.prob (y, (x, z)) (b, (a, c)) / p2 (a, c) := by
      unfold MeasureTheory.Measure.condProb MeasureTheory.Measure.prob
      rw [hdenyz]; rfl
    have hdenxz : π.map (fun ω ↦ ((x, z) ω).2) = π.map z := by congr
    have hB : π.condProb (x, z) (a, c) = p2 (a, c) / pz c := by
      unfold MeasureTheory.Measure.condProb MeasureTheory.Measure.prob
      rw [hdenxz]; rfl
    have hp2_0 : p2 (a, c) = 0 := by
      have : p2 (a, c) / pz c = 0 := by simpa [hB] using h0
      exact (ENNReal.div_eq_zero_iff.mp this).resolve_right hc_fz.ne
    have hjoint0 : π.prob (y, (x, z)) (b, (a, c)) = 0 := by
      simp [hc_my, hp2_0]
    have : π.condProb (y, (x, z)) (b, (a, c)) = (0 : ENNReal) / 0 := by
      simp [hC, hjoint0, hp2_0]
    simpa using this
  · intro htop
    have hdenxz : π.map (fun ω ↦ ((x, z) ω).2) = π.map z := by congr
    have hB : π.condProb (x, z) (a, c) = p2 (a, c) / pz c := by
      unfold MeasureTheory.Measure.condProb MeasureTheory.Measure.prob
      rw [hdenxz]; rfl
    have : π.condProb (x, z) (a, c) ≠ ⊤ := by
      if hz : pz c = 0 then
        have hp0 : p2 (a, c) = 0 := by simp [← hc_mx, hz]
        have hden0 : π.condProb (x, z) (a, c) = 0 := by simp [hB, hp0, hz]
        simp [hden0, ENNReal.zero_ne_top]
      else
        intro hden_top
        have : p2 (a, c) = ⊤ := by
          rw [← hc_mx, hden_top, ENNReal.top_mul hz]
        exact hc_fin.ne this
    exact (this htop).elim


-- created on 2023-10-13
-- updated on 2026-09-26
