import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import sympy.stats.joint_rv
open MeasureTheory Function Random
open scoped Classical


private lemma map_yy_support_diag
  [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableEq γ]
  {π : Measure Ω} {y : Ω → γ}
-- given
  (hym : AEMeasurable y π) :
-- imply
  ∀ᵐ z ∂(π.map (y, y)), z.1 = z.2 := by
-- proof
  have hyym : AEMeasurable (JointRandomSymbol y y) π :=
    (measurable_id.prodMk measurable_id).comp_aemeasurable hym
  have hp : MeasurableSet {z : γ × γ | z.1 = z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  exact (ae_map_iff hyym hp).2 (ae_of_all _ fun _ => by simp [JointRandomSymbol])


private lemma lintegral_div_mul
  [MeasurableSpace α]
  {c : ENNReal} {φ : α → ENNReal}
-- given
  (μ : Measure α)
  (hc0 : c ≠ 0)
  (hct : c ≠ ⊤)
  (hφ : Measurable φ) :
-- imply
  (∫⁻ a, φ a / c ∂μ) * c = ∫⁻ a, φ a ∂μ := by
-- proof
  calc
    _ = ∫⁻ a, (φ a / c) * c ∂μ :=
      (lintegral_mul_const c (hφ.div measurable_const)).symm
    _ = ∫⁻ a, φ a ∂μ :=
      lintegral_congr fun a ↦ ENNReal.div_mul_cancel hc0 hct

/-- Ordinary partial binder against `u ∘ y`. -/
private lemma lintegral_partialRV_mul
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  {π : Measure Ω} {x : Ω → α} {y : Ω → γ}
  {f : α → γ → ENNReal}
  {u : γ → ENNReal}
-- given
  (hP : PSpace π (x, y))
  (hf : Measurable (uncurry f))
  (hu : Measurable u) :
-- imply
  ∫⁻ ω, Expectation.partialRV π x y f ω * u (y ω) ∂π =
    ∫⁻ ω, f (x ω) (y ω) * u (y ω) ∂π := by
-- proof
  have hym : AEMeasurable y π := (PSpace.of.PSpace_Joint.snd hP).aemeasurable
  have hxym : AEMeasurable (JointRandomSymbol x y) π := hP.aemeasurable
  have hPy : PSpace π y := PSpace.of.PSpace_Joint.snd hP
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure γ := ReferenceMeasure.measure
  let p : α × γ → ENNReal := π.prob (JointRandomSymbol x y)
  let m : γ → ENNReal := π.prob y
  have hp : Measurable p := Measure.measurable_rnDeriv _ _
  have hm : Measurable m := Measure.measurable_rnDeriv _ _
  have hlaw : π.map (JointRandomSymbol x y) = (μ.prod ν).withDensity p :=
    PSpace.map_eq_withDensity_density
  have hlawy : π.map y = ν.withDensity m := PSpace.map_eq_withDensity_density
  have hden : π.map (fun ω ↦ (JointRandomSymbol x y ω).2) = π.map y := rfl
  have hunf :
      Expectation.partialRV π x y f =
        fun ω ↦ ∫⁻ a, f a (y ω) * (p (a, y ω) / m (y ω)) ∂μ := by
    funext ω
    simp only [Expectation.partialRV, Expectation.condRV, expectation_ennreal]
    have hcond :
        (fun a ↦ π.condProb (JointRandomSymbol x y) (a, y ω)) =
          fun a ↦ p (a, y ω) / m (y ω) := by
      funext a
      dsimp [Measure.condProb, Measure.prob]
      rw [hden]
      rfl
    rw [hcond]
    have hdens : Measurable fun a ↦ p (a, y ω) / m (y ω) :=
      (hp.comp (measurable_id.prodMk measurable_const)).div measurable_const
    have hf' : Measurable fun a ↦ f a (y ω) :=
      hf.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_withDensity_eq_lintegral_mul μ hdens hf']
    exact lintegral_congr fun a ↦ mul_comm _ _
  rw [hunf]
  have hslice :
      Measurable (uncurry fun a b ↦ f a b * (p (a, b) / m b)) := by
    change Measurable fun z : α × γ ↦ f z.1 z.2 * (p z / m z.2)
    exact hf.mul (hp.div (hm.comp measurable_snd))
  have hMeas : Measurable fun b ↦ (∫⁻ a, f a b * (p (a, b) / m b) ∂μ) * u b :=
    (hslice.lintegral_prod_left).mul hu
  have hmap :
      ∫⁻ ω, (∫⁻ a, f a (y ω) * (p (a, y ω) / m (y ω)) ∂μ) * u (y ω) ∂π =
        ∫⁻ b, (∫⁻ a, f a b * (p (a, b) / m b) ∂μ) * u b ∂(π.map y) :=
    (lintegral_map' hMeas.aemeasurable hym).symm
  rw [hmap, hlawy]
  have hfin : ∀ᵐ b ∂ν, m b < ⊤ := by
    have : IsProbabilityMeasure (π.map y) := Measure.isProbabilityMeasure_map hym
    have htot : ∫⁻ b, m b ∂ν = 1 := by
      have h := congrArg (fun μ : Measure γ ↦ μ Set.univ) hlawy
      rw [measure_univ, withDensity_apply (μ := ν) m MeasurableSet.univ,
        setLIntegral_univ] at h
      exact h.symm
    exact ae_lt_top hm (by rw [htot]; norm_num)
  have hcancel :
      ∫⁻ b, (∫⁻ a, f a b * (p (a, b) / m b) ∂μ) * u b ∂(ν.withDensity m) =
        ∫⁻ b, (∫⁻ a, f a b * p (a, b) ∂μ) * u b ∂ν := by
    rw [lintegral_withDensity_eq_lintegral_mul ν hm hMeas]
    -- Marginal: ∫ p(·,b) =ᵐ m
    have hmarg : (fun b ↦ ∫⁻ a, p (a, b) ∂μ) =ᵐ[ν] m := by
      have hsnd :
          Measure.map Prod.snd (π.map (JointRandomSymbol x y)) = π.map y := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hxym]
        rfl
      have hL :
          Measure.map Prod.snd ((μ.prod ν).withDensity p) =
            ν.withDensity fun b ↦ ∫⁻ a, p (a, b) ∂μ := by
        refine Measure.ext fun s hs => ?_
        rw [Measure.map_apply measurable_snd hs,
          withDensity_apply p (measurable_snd hs),
          withDensity_apply (fun b ↦ ∫⁻ a, p (a, b) ∂μ) hs]
        have hind :
            Measurable fun z : α × γ ↦
              s.indicator (fun _ ↦ (1 : ENNReal)) z.2 * p z :=
          ((measurable_one.indicator hs).comp measurable_snd).mul hp
        have h1 :
            ∫⁻ z in Prod.snd ⁻¹' s, p z ∂(μ.prod ν) =
              ∫⁻ z, s.indicator (fun _ ↦ (1 : ENNReal)) z.2 * p z ∂(μ.prod ν) := by
          rw [← lintegral_indicator (measurable_snd hs) p]
          refine lintegral_congr fun z ↦ ?_
          by_cases hz : z.2 ∈ s
          · simp [Set.indicator, hz, Set.mem_preimage]
          · simp [Set.indicator, hz, Set.mem_preimage]
        have h2 :
            ∫⁻ z, s.indicator (fun _ ↦ (1 : ENNReal)) z.2 * p z ∂(μ.prod ν) =
              ∫⁻ b, ∫⁻ a, s.indicator (fun _ ↦ (1 : ENNReal)) b * p (a, b) ∂μ ∂ν :=
          lintegral_prod_symm
            (fun z : α × γ ↦ s.indicator (fun _ ↦ (1 : ENNReal)) z.2 * p z)
            hind.aemeasurable
        have h3 :
            ∫⁻ b, ∫⁻ a, s.indicator (fun _ ↦ (1 : ENNReal)) b * p (a, b) ∂μ ∂ν =
              ∫⁻ b in s, ∫⁻ a, p (a, b) ∂μ ∂ν := by
          have hpull :
              ∫⁻ b, ∫⁻ a, s.indicator (fun _ ↦ (1 : ENNReal)) b * p (a, b) ∂μ ∂ν =
                ∫⁻ b, s.indicator (fun _ ↦ (1 : ENNReal)) b *
                  (∫⁻ a, p (a, b) ∂μ) ∂ν := by
            refine lintegral_congr fun b ↦ ?_
            simpa using (lintegral_const_mul''
              (s.indicator (fun _ ↦ (1 : ENNReal)) b)
              (hp.comp (measurable_id.prodMk measurable_const)).aemeasurable)
          rw [hpull]
          have hind' :
              ∫⁻ b, s.indicator (fun _ ↦ (1 : ENNReal)) b *
                  (∫⁻ a, p (a, b) ∂μ) ∂ν =
                ∫⁻ b, s.indicator (fun b ↦ ∫⁻ a, p (a, b) ∂μ) b ∂ν := by
            refine lintegral_congr fun b ↦ ?_
            by_cases hb : b ∈ s <;> simp [Set.indicator, hb]
          rw [hind', lintegral_indicator hs]
        exact h1.trans (h2.trans h3)
      have hμeq :
          ν.withDensity m = ν.withDensity fun b ↦ ∫⁻ a, p (a, b) ∂μ := by
        calc
          ν.withDensity m = π.map y := hlawy.symm
          _ = Measure.map Prod.snd (π.map (JointRandomSymbol x y)) := hsnd.symm
          _ = Measure.map Prod.snd ((μ.prod ν).withDensity p) := by rw [hlaw]
          _ = ν.withDensity fun b ↦ ∫⁻ a, p (a, b) ∂μ := hL
      have hmInt : Measurable fun b ↦ ∫⁻ a, p (a, b) ∂μ :=
        (show Measurable (uncurry fun a b ↦ p (a, b)) from hp).lintegral_prod_left
      exact ((withDensity_eq_iff_of_sigmaFinite hm.aemeasurable hmInt.aemeasurable).1
        hμeq).symm
    refine lintegral_congr_ae ?_
    filter_upwards [hfin, hmarg] with b hb hmargeq
    simp only [Pi.mul_apply]
    have hre : m b * ((∫⁻ a, f a b * (p (a, b) / m b) ∂μ) * u b) =
        ((∫⁻ a, f a b * (p (a, b) / m b) ∂μ) * u b) * m b := mul_comm _ _
    rw [hre, mul_assoc, mul_comm (u b) (m b), ← mul_assoc]
    congr 1
    have hφ : Measurable fun a ↦ f a b * p (a, b) :=
      (hf.comp (measurable_id.prodMk measurable_const)).mul
        (hp.comp (measurable_id.prodMk measurable_const))
    by_cases h0 : m b = 0
    · have hpint : ∫⁻ a, p (a, b) ∂μ = 0 := by rw [hmargeq, h0]
      have hp0 : (fun a ↦ p (a, b)) =ᵐ[μ] 0 :=
        (lintegral_eq_zero_iff
          (hp.comp (measurable_id.prodMk measurable_const))).1 hpint
      simp [h0]
      -- goal: 0 = ∫⁻ a, f a b * p (a, b) ∂μ
      refine Eq.symm ((lintegral_eq_zero_iff hφ).2 ?_)
      filter_upwards [hp0] with a ha
      simp [ha]
    · have : (∫⁻ a, f a b * (p (a, b) / m b) ∂μ) * m b =
          (∫⁻ a, (f a b * p (a, b)) / m b ∂μ) * m b := by
        refine congrArg (· * m b) (lintegral_congr fun a ↦ ?_)
        exact (mul_div_assoc (f a b) (p (a, b)) (m b)).symm
      rw [this]
      exact lintegral_div_mul μ h0 hb.ne hφ
  rw [hcancel]
  have hφ2 : Measurable fun z : α × γ ↦ f z.1 z.2 * p z * u z.2 :=
    (hf.mul hp).mul (hu.comp measurable_snd)
  have hFub :
      ∫⁻ b, (∫⁻ a, f a b * p (a, b) ∂μ) * u b ∂ν =
        ∫⁻ z, f z.1 z.2 * p z * u z.2 ∂(μ.prod ν) := by
    have : ∫⁻ b, (∫⁻ a, f a b * p (a, b) ∂μ) * u b ∂ν =
        ∫⁻ b, ∫⁻ a, f a b * p (a, b) * u b ∂μ ∂ν := by
      refine lintegral_congr fun b ↦ ?_
      exact (lintegral_mul_const (u b)
        ((hf.comp (measurable_id.prodMk measurable_const)).mul
          (hp.comp (measurable_id.prodMk measurable_const)))).symm
    rw [this]
    exact (lintegral_prod_symm (fun z : α × γ ↦ f z.1 z.2 * p z * u z.2)
      hφ2.aemeasurable).symm
  have hobs : Measurable fun z : α × γ ↦ f z.1 z.2 * u z.2 :=
    hf.mul (hu.comp measurable_snd)
  have hwd :
      ∫⁻ z, f z.1 z.2 * p z * u z.2 ∂(μ.prod ν) =
        ∫⁻ z, f z.1 z.2 * u z.2 ∂((μ.prod ν).withDensity p) := by
    have : ∫⁻ z, f z.1 z.2 * p z * u z.2 ∂(μ.prod ν) =
        ∫⁻ z, p z * (f z.1 z.2 * u z.2) ∂(μ.prod ν) := by
      refine lintegral_congr fun z ↦ ?_
      ac_rfl
    rw [this]
    exact (lintegral_withDensity_eq_lintegral_mul (μ.prod ν) hp hobs).symm
  rw [hFub, hwd, ← hlaw]
  rw [lintegral_map' hobs.aemeasurable hxym]
  refine lintegral_congr fun ω ↦ ?_
  simp [JointRandomSymbol]

/-- RA partial binder (redundant `| y`) against `u ∘ y`. -/
private lemma lintegral_partialRV_RA_mul
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  {π : Measure Ω} {x : Ω → α} {y : Ω → γ}
  {f : α → γ → ENNReal}
  {u : γ → ENNReal}
-- given
  (hPyy : PSpace π (x, y, y))
  (hf : Measurable (uncurry f))
  (hu : Measurable u) :
-- imply
  ∫⁻ ω, Expectation.partialRV_RA π x y y f ω * u (y ω) ∂π =
    ∫⁻ ω, f (x ω) (y ω) * u (y ω) ∂π := by
-- proof
  have hyym : AEMeasurable (JointRandomSymbol y y) π :=
    (PSpace.of.PSpace_Joint.snd hPyy).aemeasurable
  have hxyym : AEMeasurable (JointRandomSymbol x (JointRandomSymbol y y)) π :=
    hPyy.aemeasurable
  have hPyy2 : PSpace π (y, y) := PSpace.of.PSpace_Joint.snd hPyy
  have hym : AEMeasurable y π := (PSpace.of.PSpace_Joint.fst hPyy2).aemeasurable
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure γ := ReferenceMeasure.measure
  let νν : Measure (γ × γ) := ReferenceMeasure.measure
  let p' : α × (γ × γ) → ENNReal :=
    π.prob (JointRandomSymbol x (JointRandomSymbol y y))
  let m' : γ × γ → ENNReal := π.prob (JointRandomSymbol y y)
  have hp' : Measurable p' := Measure.measurable_rnDeriv _ _
  have hm' : Measurable m' := Measure.measurable_rnDeriv _ _
  have hlaw : π.map (JointRandomSymbol x (JointRandomSymbol y y)) =
      (μ.prod νν).withDensity p' := PSpace.map_eq_withDensity_density
  have hlawyy : π.map (JointRandomSymbol y y) = νν.withDensity m' :=
    PSpace.map_eq_withDensity_density
  have hden :
      π.map (fun ω ↦ (JointRandomSymbol x (JointRandomSymbol y y) ω).2) =
        π.map (JointRandomSymbol y y) := rfl
  have hunf :
      Expectation.partialRV_RA π x y y f =
        fun ω ↦ ∫⁻ a, f a (y ω) * (p' (a, (y ω, y ω)) / m' (y ω, y ω)) ∂μ := by
    funext ω
    simp only [Expectation.partialRV_RA, Expectation.partialRV_cond, expectation_ennreal]
    have hcond :
        (fun a ↦ π.condProb (JointRandomSymbol x (JointRandomSymbol y y))
            (a, (y ω, y ω))) =
          fun a ↦ p' (a, (y ω, y ω)) / m' (y ω, y ω) := by
      funext a
      dsimp [Measure.condProb, Measure.prob]
      rw [hden]
      simp [p', m', Measure.prob]
    rw [hcond]
    have hdens : Measurable fun a ↦ p' (a, (y ω, y ω)) / m' (y ω, y ω) :=
      (hp'.comp (measurable_id.prodMk measurable_const)).div measurable_const
    have hf' : Measurable fun a ↦ f a (y ω) :=
      hf.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_withDensity_eq_lintegral_mul μ hdens hf']
    exact lintegral_congr fun a ↦ mul_comm _ _
  rw [hunf]
  have hslice :
      Measurable (uncurry fun a (z : γ × γ) ↦ f a z.1 * (p' (a, z) / m' z)) := by
    change Measurable fun w : α × (γ × γ) ↦ f w.1 w.2.1 * (p' w / m' w.2)
    exact (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hp'.div (hm'.comp measurable_snd))
  have hMeas :
      Measurable fun z : γ × γ ↦
        (∫⁻ a, f a z.1 * (p' (a, z) / m' z) ∂μ) * u z.1 :=
    (hslice.lintegral_prod_left).mul (hu.comp measurable_fst)
  have hmap :
      ∫⁻ ω, (∫⁻ a, f a (y ω) * (p' (a, (y ω, y ω)) / m' (y ω, y ω)) ∂μ) *
          u (y ω) ∂π =
        ∫⁻ z, (∫⁻ a, f a z.1 * (p' (a, z) / m' z) ∂μ) * u z.1
          ∂(π.map (JointRandomSymbol y y)) := by
    have : JointRandomSymbol y y = fun ω ↦ (y ω, y ω) := rfl
    simpa [this] using (lintegral_map' hMeas.aemeasurable hyym).symm
  rw [hmap, hlawyy]
  have hfin : ∀ᵐ z ∂νν, m' z < ⊤ := by
    have : IsProbabilityMeasure (π.map (JointRandomSymbol y y)) :=
      Measure.isProbabilityMeasure_map hyym
    have htot : ∫⁻ z, m' z ∂νν = 1 := by
      have h := congrArg (fun μ : Measure (γ × γ) ↦ μ Set.univ) hlawyy
      rw [measure_univ, withDensity_apply (μ := νν) m' MeasurableSet.univ,
        setLIntegral_univ] at h
      exact h.symm
    exact ae_lt_top hm' (by rw [htot]; norm_num)
  have hcancel :
      ∫⁻ z, (∫⁻ a, f a z.1 * (p' (a, z) / m' z) ∂μ) * u z.1 ∂(νν.withDensity m') =
        ∫⁻ z, (∫⁻ a, f a z.1 * p' (a, z) ∂μ) * u z.1 ∂νν := by
    rw [lintegral_withDensity_eq_lintegral_mul νν hm' hMeas]
    have hmarg : (fun z ↦ ∫⁻ a, p' (a, z) ∂μ) =ᵐ[νν] m' := by
      have hsnd :
          Measure.map Prod.snd (π.map (JointRandomSymbol x (JointRandomSymbol y y))) =
            π.map (JointRandomSymbol y y) := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hxyym]
        rfl
      have hL :
          Measure.map Prod.snd ((μ.prod νν).withDensity p') =
            νν.withDensity fun z ↦ ∫⁻ a, p' (a, z) ∂μ := by
        refine Measure.ext fun s hs => ?_
        rw [Measure.map_apply measurable_snd hs,
          withDensity_apply p' (measurable_snd hs),
          withDensity_apply (fun z ↦ ∫⁻ a, p' (a, z) ∂μ) hs]
        have hind :
            Measurable fun w : α × (γ × γ) ↦
              s.indicator (fun _ ↦ (1 : ENNReal)) w.2 * p' w :=
          ((measurable_one.indicator hs).comp measurable_snd).mul hp'
        have h1 :
            ∫⁻ w in Prod.snd ⁻¹' s, p' w ∂(μ.prod νν) =
              ∫⁻ w, s.indicator (fun _ ↦ (1 : ENNReal)) w.2 * p' w ∂(μ.prod νν) := by
          rw [← lintegral_indicator (measurable_snd hs) p']
          refine lintegral_congr fun w ↦ ?_
          by_cases hz : w.2 ∈ s
          · simp [Set.indicator, hz, Set.mem_preimage]
          · simp [Set.indicator, hz, Set.mem_preimage]
        have h2 :
            ∫⁻ w, s.indicator (fun _ ↦ (1 : ENNReal)) w.2 * p' w ∂(μ.prod νν) =
              ∫⁻ z, ∫⁻ a, s.indicator (fun _ ↦ (1 : ENNReal)) z * p' (a, z) ∂μ ∂νν :=
          lintegral_prod_symm
            (fun w : α × (γ × γ) ↦ s.indicator (fun _ ↦ (1 : ENNReal)) w.2 * p' w)
            hind.aemeasurable
        have h3 :
            ∫⁻ z, ∫⁻ a, s.indicator (fun _ ↦ (1 : ENNReal)) z * p' (a, z) ∂μ ∂νν =
              ∫⁻ z in s, ∫⁻ a, p' (a, z) ∂μ ∂νν := by
          have hpull :
              ∫⁻ z, ∫⁻ a, s.indicator (fun _ ↦ (1 : ENNReal)) z * p' (a, z) ∂μ ∂νν =
                ∫⁻ z, s.indicator (fun _ ↦ (1 : ENNReal)) z *
                  (∫⁻ a, p' (a, z) ∂μ) ∂νν := by
            refine lintegral_congr fun z ↦ ?_
            simpa using (lintegral_const_mul''
              (s.indicator (fun _ ↦ (1 : ENNReal)) z)
              (hp'.comp (measurable_id.prodMk measurable_const)).aemeasurable)
          rw [hpull]
          have hind' :
              ∫⁻ z, s.indicator (fun _ ↦ (1 : ENNReal)) z *
                  (∫⁻ a, p' (a, z) ∂μ) ∂νν =
                ∫⁻ z, s.indicator (fun z ↦ ∫⁻ a, p' (a, z) ∂μ) z ∂νν := by
            refine lintegral_congr fun z ↦ ?_
            by_cases hz : z ∈ s <;> simp [Set.indicator, hz]
          rw [hind', lintegral_indicator hs]
        exact h1.trans (h2.trans h3)
      have hμeq :
          νν.withDensity m' = νν.withDensity fun z ↦ ∫⁻ a, p' (a, z) ∂μ := by
        calc
          νν.withDensity m' = π.map (JointRandomSymbol y y) := hlawyy.symm
          _ = Measure.map Prod.snd
                (π.map (JointRandomSymbol x (JointRandomSymbol y y))) := hsnd.symm
          _ = Measure.map Prod.snd ((μ.prod νν).withDensity p') := by rw [hlaw]
          _ = νν.withDensity fun z ↦ ∫⁻ a, p' (a, z) ∂μ := hL
      have hmInt : Measurable fun z ↦ ∫⁻ a, p' (a, z) ∂μ :=
        (show Measurable (uncurry fun a z ↦ p' (a, z)) from hp').lintegral_prod_left
      exact ((withDensity_eq_iff_of_sigmaFinite hm'.aemeasurable hmInt.aemeasurable).1
        hμeq).symm
    refine lintegral_congr_ae ?_
    filter_upwards [hfin, hmarg] with z hz hmargeq
    simp only [Pi.mul_apply]
    have hre : m' z * ((∫⁻ a, f a z.1 * (p' (a, z) / m' z) ∂μ) * u z.1) =
        ((∫⁻ a, f a z.1 * (p' (a, z) / m' z) ∂μ) * u z.1) * m' z := mul_comm _ _
    rw [hre, mul_assoc, mul_comm (u z.1) (m' z), ← mul_assoc]
    congr 1
    have hφ : Measurable fun a ↦ f a z.1 * p' (a, z) :=
      (hf.comp (measurable_id.prodMk measurable_const)).mul
        (hp'.comp (measurable_id.prodMk measurable_const))
    by_cases h0 : m' z = 0
    · have hpint : ∫⁻ a, p' (a, z) ∂μ = 0 := by rw [hmargeq, h0]
      have hp0 : (fun a ↦ p' (a, z)) =ᵐ[μ] 0 :=
        (lintegral_eq_zero_iff
          (hp'.comp (measurable_id.prodMk measurable_const))).1 hpint
      simp [h0]
      refine Eq.symm ((lintegral_eq_zero_iff hφ).2 ?_)
      filter_upwards [hp0] with a ha
      simp [ha]
    · have : (∫⁻ a, f a z.1 * (p' (a, z) / m' z) ∂μ) * m' z =
          (∫⁻ a, (f a z.1 * p' (a, z)) / m' z ∂μ) * m' z := by
        refine congrArg (· * m' z) (lintegral_congr fun a ↦ ?_)
        exact (mul_div_assoc (f a z.1) (p' (a, z)) (m' z)).symm
      rw [this]
      exact lintegral_div_mul μ h0 hz.ne hφ
  rw [hcancel]
  have hφ2 : Measurable fun w : α × (γ × γ) ↦ f w.1 w.2.1 * p' w * u w.2.1 := by
    refine (Measurable.mul ?_ hp').mul (hu.comp (measurable_fst.comp measurable_snd))
    exact hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hFub :
      ∫⁻ z, (∫⁻ a, f a z.1 * p' (a, z) ∂μ) * u z.1 ∂νν =
        ∫⁻ w, f w.1 w.2.1 * p' w * u w.2.1 ∂(μ.prod νν) := by
    have : ∫⁻ z, (∫⁻ a, f a z.1 * p' (a, z) ∂μ) * u z.1 ∂νν =
        ∫⁻ z, ∫⁻ a, f a z.1 * p' (a, z) * u z.1 ∂μ ∂νν := by
      refine lintegral_congr fun z ↦ ?_
      exact (lintegral_mul_const (u z.1)
        ((hf.comp (measurable_id.prodMk measurable_const)).mul
          (hp'.comp (measurable_id.prodMk measurable_const)))).symm
    rw [this]
    exact (lintegral_prod_symm
      (fun w : α × (γ × γ) ↦ f w.1 w.2.1 * p' w * u w.2.1)
      hφ2.aemeasurable).symm
  have hobs : Measurable fun w : α × (γ × γ) ↦ f w.1 w.2.1 * u w.2.1 :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hu.comp (measurable_fst.comp measurable_snd))
  have hwd :
      ∫⁻ w, f w.1 w.2.1 * p' w * u w.2.1 ∂(μ.prod νν) =
        ∫⁻ w, f w.1 w.2.1 * u w.2.1 ∂((μ.prod νν).withDensity p') := by
    have : ∫⁻ w, f w.1 w.2.1 * p' w * u w.2.1 ∂(μ.prod νν) =
        ∫⁻ w, p' w * (f w.1 w.2.1 * u w.2.1) ∂(μ.prod νν) := by
      refine lintegral_congr fun w ↦ ?_
      ac_rfl
    rw [this]
    exact (lintegral_withDensity_eq_lintegral_mul (μ.prod νν) hp' hobs).symm
  rw [hFub, hwd, ← hlaw]
  rw [lintegral_map' hobs.aemeasurable hxyym]
  refine lintegral_congr fun ω ↦ ?_
  simp [JointRandomSymbol]

@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  {π : Measure Ω} {x : Ω → α} {y : Ω → γ}
  {f : α → γ → ENNReal}
-- given
  (hP : PSpace π (x, y))
  (hPyy : PSpace π (x, y, y))
  (hf : Measurable (uncurry f)) :
-- imply
  𝔼[x: π | y](f x y | y) =ᵐ[π] 𝔼[x: π | y](f x y) := by
-- proof
  change Expectation.partialRV_RA π x y y f =ᵐ[π] Expectation.partialRV π x y f
  have hym : AEMeasurable y π := (PSpace.of.PSpace_Joint.snd hP).aemeasurable
  have hPy : PSpace π y := PSpace.of.PSpace_Joint.snd hP
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure γ := ReferenceMeasure.measure
  have hPyy2 : PSpace π (y, y) := PSpace.of.PSpace_Joint.snd hPyy
  let p : α × γ → ENNReal := π.prob (JointRandomSymbol x y)
  let m : γ → ENNReal := π.prob y
  let p' : α × (γ × γ) → ENNReal :=
    π.prob (JointRandomSymbol x (JointRandomSymbol y y))
  let m' : γ × γ → ENNReal := π.prob (JointRandomSymbol y y)
  have hp : Measurable p := Measure.measurable_rnDeriv _ _
  have hm : Measurable m := Measure.measurable_rnDeriv _ _
  have hp' : Measurable p' := Measure.measurable_rnDeriv _ _
  have hm' : Measurable m' := Measure.measurable_rnDeriv _ _
  let g : γ → ENNReal := fun b ↦ ∫⁻ a, f a b * (p (a, b) / m b) ∂μ
  let g' : γ → ENNReal :=
    fun b ↦ ∫⁻ a, f a b * (p' (a, (b, b)) / m' (b, b)) ∂μ
  have hg : Measurable g := by
    change Measurable fun b ↦ ∫⁻ a, f a b * (p (a, b) / m b) ∂μ
    exact (hf.mul (hp.div (hm.comp measurable_snd))).lintegral_prod_left
  have hg' : Measurable g' := by
    have hslice :
        Measurable (uncurry fun a b ↦ f a b * (p' (a, (b, b)) / m' (b, b))) := by
      change Measurable fun z : α × γ ↦
        f z.1 z.2 * (p' (z.1, (z.2, z.2)) / m' (z.2, z.2))
      have hdiag : Measurable fun b : γ ↦ (b, b) := measurable_id.prodMk measurable_id
      exact hf.mul
        ((hp'.comp (measurable_fst.prodMk (hdiag.comp measurable_snd))).div
          (hm'.comp (hdiag.comp measurable_snd)))
    exact hslice.lintegral_prod_left
  have hunf :
      Expectation.partialRV π x y f = fun ω ↦ g (y ω) := by
    funext ω
    simp only [g]
    have h := lintegral_partialRV_mul (u := fun _ ↦ 1) hP hf measurable_const
    -- better: reuse unfold from helper — do direct unfold
    simp only [Expectation.partialRV, Expectation.condRV, expectation_ennreal]
    have hden : π.map (fun ω ↦ (JointRandomSymbol x y ω).2) = π.map y := rfl
    have hcond :
        (fun a ↦ π.condProb (JointRandomSymbol x y) (a, y ω)) =
          fun a ↦ p (a, y ω) / m (y ω) := by
      funext a
      dsimp [Measure.condProb, Measure.prob]
      rw [hden]
      rfl
    rw [hcond]
    have hdens : Measurable fun a ↦ p (a, y ω) / m (y ω) :=
      (hp.comp (measurable_id.prodMk measurable_const)).div measurable_const
    have hf' : Measurable fun a ↦ f a (y ω) :=
      hf.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_withDensity_eq_lintegral_mul μ hdens hf']
    exact lintegral_congr fun a ↦ mul_comm _ _
  have hunf' :
      Expectation.partialRV_RA π x y y f = fun ω ↦ g' (y ω) := by
    funext ω
    simp only [g', Expectation.partialRV_RA, Expectation.partialRV_cond,
      expectation_ennreal]
    have hden :
        π.map (fun ω ↦ (JointRandomSymbol x (JointRandomSymbol y y) ω).2) =
          π.map (JointRandomSymbol y y) := rfl
    have hcond :
        (fun a ↦ π.condProb (JointRandomSymbol x (JointRandomSymbol y y))
            (a, (y ω, y ω))) =
          fun a ↦ p' (a, (y ω, y ω)) / m' (y ω, y ω) := by
      funext a
      dsimp [Measure.condProb, Measure.prob]
      rw [hden]
      simp [p', m', Measure.prob]
    rw [hcond]
    have hdens : Measurable fun a ↦ p' (a, (y ω, y ω)) / m' (y ω, y ω) :=
      (hp'.comp (measurable_id.prodMk measurable_const)).div measurable_const
    have hf' : Measurable fun a ↦ f a (y ω) :=
      hf.comp (measurable_id.prodMk measurable_const)
    rw [lintegral_withDensity_eq_lintegral_mul μ hdens hf']
    exact lintegral_congr fun a ↦ mul_comm _ _
  have hlawy : π.map y = ν.withDensity m := PSpace.map_eq_withDensity_density
  have hgg' : g =ᵐ[π.map y] g' := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg hg' ?_
    intro s hs _
    have hu : Measurable (s.indicator fun _ ↦ (1 : ENNReal)) :=
      measurable_one.indicator hs
    have hL := lintegral_partialRV_mul hP hf hu
    have hR := lintegral_partialRV_RA_mul hPyy hf hu
    have hEq := hL.trans hR.symm
    have hmapg :
        ∫⁻ ω, Expectation.partialRV π x y f ω *
            s.indicator (fun _ ↦ (1 : ENNReal)) (y ω) ∂π =
          ∫⁻ b in s, g b ∂(π.map y) := by
      rw [hunf]
      have :
          ∫⁻ ω, g (y ω) * s.indicator (fun _ ↦ (1 : ENNReal)) (y ω) ∂π =
            ∫⁻ b, g b * s.indicator (fun _ ↦ (1 : ENNReal)) b ∂(π.map y) :=
        (lintegral_map' (hg.mul hu).aemeasurable hym).symm
      rw [this]
      have hInd :
          (fun b ↦ g b * s.indicator (fun _ ↦ (1 : ENNReal)) b) =
            s.indicator g := by
        funext b
        by_cases hb : b ∈ s <;> simp [Set.indicator, hb]
      rw [hInd, lintegral_indicator hs]
    have hmapg' :
        ∫⁻ ω, Expectation.partialRV_RA π x y y f ω *
            s.indicator (fun _ ↦ (1 : ENNReal)) (y ω) ∂π =
          ∫⁻ b in s, g' b ∂(π.map y) := by
      rw [hunf']
      have :
          ∫⁻ ω, g' (y ω) * s.indicator (fun _ ↦ (1 : ENNReal)) (y ω) ∂π =
            ∫⁻ b, g' b * s.indicator (fun _ ↦ (1 : ENNReal)) b ∂(π.map y) :=
        (lintegral_map' (hg'.mul hu).aemeasurable hym).symm
      rw [this]
      have hInd :
          (fun b ↦ g' b * s.indicator (fun _ ↦ (1 : ENNReal)) b) =
            s.indicator g' := by
        funext b
        by_cases hb : b ∈ s <;> simp [Set.indicator, hb]
      rw [hInd, lintegral_indicator hs]
    exact (hmapg.symm.trans hEq).trans hmapg'
  rw [hunf, hunf']
  exact (ae_eq_comp hym hgg').symm


-- created on 2026-09-20
