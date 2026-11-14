import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Kernel.Composition.WithDensity
import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
import Lemma.Random.ExpectCond.eq.Integral_Mul_ProbCond
open MeasureTheory ProbabilityTheory Random
open scoped ENNReal.ToRealCoe


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α] [ν : ReferenceMeasure β]
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ] [MeasurableSpace ℰ] [BorelSpace ℰ]
  [StandardBorelSpace α] [Nonempty α]
  {π : Measure Ω}
  {a : Ω → α} {s : Ω → β}
  {f : α → ℰ}
-- given
  (hP : SinglePSpace π (a, s))
  (hf : Measurable f) :
-- imply
  ∀ᵐ «\sf{s}» ∂(π.map s),
    𝔼[a: π](f a | s = «\sf{s}») =
      ∫ «\sf{a}», (ℙ[π](a = «\sf{a}» | s = «\sf{s}») : ℝ) • f «\sf{a}» ∂μ.measure := by
-- proof
  have := hf
  have ha : AEMeasurable a π := (PSpace.aemeasurable (x := (a, s))).fst
  have hs : AEMeasurable s π := (PSpace.aemeasurable (x := (a, s))).snd
  have hPs : SinglePSpace π s := SinglePSpace.of.SinglePSpace.snd hP
  let μα : Measure α := μ.measure
  let νβ : Measure β := ν.measure
  obtain ⟨p, Dp, hjoint₀⟩ := hP.exists_distribution
  have hp : Measurable p := Dp
  have hjoint : π.map (a, s) = (μα.prod νβ).withDensity p := hjoint₀
  let q : β → ENNReal := fun b ↦ ∫⁻ x, p (x, b) ∂μα
  have hq : Measurable q := hp.lintegral_prod_left'
  have hmap : π.map s = (π.map (a, s)).map Prod.snd :=
    (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      hP.aemeasurable).symm
  have hlaw : π.map s = νβ.withDensity q := by
    rw [hmap, hjoint]
    have hmarg : νβ.withDensity (fun y ↦ lintegral μα (fun x ↦ p (x, y))) =
      ((μα.prod νβ).withDensity p).snd := by
      ext t ht
      rw [withDensity_apply _ ht]
      have h : ((μα.prod νβ).withDensity p).snd t =
        lintegral (νβ.restrict t) (fun y ↦ lintegral μα (fun x ↦ p (x, y))) := by
        rw [Measure.snd_apply ht, ← Set.univ_prod,
          withDensity_apply _ (MeasurableSet.prod MeasurableSet.univ ht),
          setLIntegral_prod_symm p hp.aemeasurable.restrict]
        simp only [setLIntegral_univ]
      exact h.symm
    exact hmarg.symm
  have htot : ∫⁻ b, q b ∂νβ = 1 := by
    have h : (νβ.withDensity q) Set.univ = ∫⁻ b, q b ∂νβ := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [← h, ← hlaw]
    have : IsProbabilityMeasure (π.map s) := inferInstance
    exact measure_univ
  have hfin : ∀ᵐ b ∂νβ, q b < ⊤ :=
    ae_lt_top hq (by rw [htot]; norm_num)
  let g : β → α → ENNReal := fun s0 a0 ↦
    if q s0 ≠ 0 ∧ q s0 ≠ ⊤ ∧ p (a0, s0) ≠ ⊤ then p (a0, s0) / q s0 else 0
  have hg' : Measurable (Function.uncurry g) := by
    have hφ : Measurable fun z : β × α ↦ p (z.2, z.1) / q z.1 :=
      (hp.comp (Measurable.prodMk measurable_snd measurable_fst)).div
        (hq.comp measurable_fst)
    have h0 : MeasurableSet {z : β × α | q z.1 ≠ 0} :=
      ((hq.comp measurable_fst) (measurableSet_singleton (0 : ENNReal))).compl
    have htop : MeasurableSet {z : β × α | q z.1 < ⊤} :=
      (hq.comp measurable_fst) measurableSet_Iio
    have htop' : MeasurableSet {z : β × α | q z.1 ≠ ⊤} := by
      convert htop using 1
      ext z
      exact lt_top_iff_ne_top.symm
    have hpfin : MeasurableSet {z : β × α | p (z.2, z.1) < ⊤} :=
      (hp.comp (Measurable.prodMk measurable_snd measurable_fst)) measurableSet_Iio
    have hpfin' : MeasurableSet {z : β × α | p (z.2, z.1) ≠ ⊤} := by
      convert hpfin using 1
      ext z
      exact lt_top_iff_ne_top.symm
    exact Measurable.ite (h0.inter (htop'.inter hpfin')) hφ measurable_const
  have hg_ne_top : ∀ s0 a0, g s0 a0 ≠ ⊤ := by
    intro s0 a0
    change (if q s0 ≠ 0 ∧ q s0 ≠ ⊤ ∧ p (a0, s0) ≠ ⊤ then
      p (a0, s0) / q s0 else 0) ≠ ⊤
    split_ifs with h
    · exact ENNReal.div_ne_top h.2.2 h.1
    · exact ENNReal.zero_ne_top
  let κ : Kernel β α := Kernel.withDensity (Kernel.const β μα) g
  have : IsSFiniteKernel κ := Kernel.IsSFiniteKernel.withDensity _ hg_ne_top
  have : IsFiniteKernel κ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun s0 ↦ ?_⟩⟩
    rw [Kernel.withDensity_apply _ hg' s0, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ, Kernel.const_apply]
    change ∫⁻ a0, g s0 a0 ∂μα ≤ 1
    if h0 : q s0 = 0 then
      simp [g, h0]
    else if htop : q s0 = ⊤ then
      simp [g, htop]
    else
      have hle : (fun a0 ↦ g s0 a0) ≤ fun a0 ↦ p (a0, s0) / q s0 := by
        intro a0
        if hpn : p (a0, s0) ≠ ⊤ then
          simp [g, h0, htop, hpn]
        else
          simp [g, h0, htop, hpn]
      refine (lintegral_mono hle).trans ?_
      have hr : (q s0)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
      have hdiv : (fun a0 ↦ p (a0, s0) / q s0) =
        fun a0 ↦ (q s0)⁻¹ * p (a0, s0) := by
        funext a0
        exact ENNReal.div_eq_inv_mul
      rw [hdiv, lintegral_const_mul' _ _ hr]
      have hqI : ∫⁻ a0, p (a0, s0) ∂μα = q s0 := rfl
      rw [hqI, ENNReal.inv_mul_cancel h0 htop]
  have hzero : ∀ᵐ b ∂νβ, ∀ᵐ x ∂μα, q b = 0 → p (x, b) = 0 := by
    filter_upwards with b
    if h0 : q b = 0 then
      have hpb : Measurable (fun x : α ↦ p (x, b)) :=
        hp.comp (Measurable.prodMk measurable_id measurable_const)
      exact ((lintegral_eq_zero_iff hpb).mp h0).mono fun x hx _ ↦ hx
    else
      exact Filter.Eventually.of_forall fun _ h ↦ (h0 h).elim
  have h1 : MeasurableSet {z : β × α | q z.1 = 0} :=
    (hq.comp measurable_fst) (measurableSet_singleton (0 : ENNReal))
  have h2 : MeasurableSet {z : β × α | p (z.2, z.1) = 0} :=
    (hp.comp (Measurable.prodMk measurable_snd measurable_fst))
      (measurableSet_singleton (0 : ENNReal))
  have hPms : MeasurableSet {z : β × α | q z.1 = 0 → p (z.2, z.1) = 0} := by
    convert h1.compl.union h2 using 1
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union]
    exact imp_iff_not_or
  have hzero' : ∀ᵐ z ∂(νβ.prod μα), q z.1 = 0 → p z.swap = 0 :=
    (Measure.ae_prod_iff_ae_ae hPms).mpr hzero
  have hfinp : ∀ᵐ z ∂(νβ.prod μα), q z.1 < ⊤ := by
    exact (Measure.ae_prod_iff_ae_ae
        ((hq.comp measurable_fst) measurableSet_Iio)).mpr <| by
      filter_upwards [hfin] with b hb
      exact Filter.Eventually.of_forall fun _ ↦ hb
  have hptop : ∀ᵐ z ∂(νβ.prod μα), q z.1 ≠ ⊤ → p z.swap ≠ ⊤ := by
    have hqtop : MeasurableSet {z : β × α | q z.1 ≠ ⊤} := by
      convert (hq.comp measurable_fst) measurableSet_Iio using 1
      ext z
      exact lt_top_iff_ne_top.symm
    have hpnset : MeasurableSet {z : β × α | p (z.2, z.1) ≠ ⊤} := by
      convert (hp.comp (Measurable.prodMk measurable_snd measurable_fst))
        measurableSet_Iio using 1
      ext z
      exact lt_top_iff_ne_top.symm
    have hms : MeasurableSet {z : β × α | q z.1 ≠ ⊤ → p (z.2, z.1) ≠ ⊤} := by
      convert hqtop.compl.union hpnset using 1
      ext z
      simp only [Set.mem_compl_iff, Set.mem_union]
      exact imp_iff_not_or
    exact (Measure.ae_prod_iff_ae_ae hms).mpr <| by
      filter_upwards with b
      if ht : q b = ⊤ then
        exact Filter.Eventually.of_forall fun _ h ↦ (h ht).elim
      else
        have hpb : Measurable (fun x : α ↦ p (x, b)) :=
          hp.comp (Measurable.prodMk measurable_id measurable_const)
        exact (ae_lt_top hpb ht).mono fun _ hlt _ ↦ hlt.ne
  have hdens :
    (fun z : β × α ↦ q z.1 * g z.1 z.2) =ᵐ[νβ.prod μα] fun z ↦ p z.swap := by
    filter_upwards [hzero', hfinp, hptop] with z hz0 hfinz hptopz
    change q z.1 * g z.1 z.2 = p z.swap
    if h0 : q z.1 = 0 then
      have : p z.swap = 0 := hz0 h0
      simp [g, h0, this]
    else
      have hne : q z.1 ≠ ⊤ := hfinz.ne
      have hpne : p (z.2, z.1) ≠ ⊤ := hptopz hne
      have hg : g z.1 z.2 = p (z.2, z.1) / q z.1 := by
        simp [g, h0, hne, hpne]
      rw [hg, ENNReal.mul_div_cancel h0 hne]
      rfl
  have hmap_sa :
    π.map (fun ω ↦ (s ω, a ω)) =
        (νβ.prod μα).withDensity (fun z ↦ p z.swap) := by
    have hsw :
      π.map (fun ω ↦ (s ω, a ω)) = (π.map (a, s)).map Prod.swap := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable
        hP.aemeasurable]
      rfl
    rw [hsw, hjoint]
    ext t ht
    have hμν := Measure.measurePreserving_swap (μ := μα) (ν := νβ)
    rw [Measure.map_apply measurable_swap ht,
      withDensity_apply _ (measurable_swap ht),
      withDensity_apply _ ht,
      ← lintegral_indicator (measurable_swap ht),
      ← lintegral_indicator ht]
    have hmeas : Measurable fun y : β × α ↦ t.indicator (fun z ↦ p z.swap) y :=
      (hp.comp measurable_swap).indicator ht
    have hfun :
      (fun a : α × β ↦ t.indicator (fun z ↦ p z.swap) (Prod.swap a)) =
          (Prod.swap ⁻¹' t).indicator p := by
      classical
      ext a
      rfl
    exact hfun ▸ hμν.lintegral_comp hmeas
  have hprod : π.map (fun ω ↦ (s ω, a ω)) = π.map s ⊗ₘ κ := by
    have hcomp :
      (νβ.withDensity q) ⊗ₘ κ =
          (νβ.prod μα).withDensity (fun z ↦ q z.1 * g z.1 z.2) := by
      rw [← Measure.compProd_const (μ := νβ) (ν := μα),
        Measure.withDensity_compProd_withDensity (κ := Kernel.const β μα) hq hg']
    rw [hlaw, hcomp, withDensity_congr_ae hdens, hmap_sa]
  have hκ : condDistrib a s π =ᵐ[π.map s] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd hs ha hprod
  have hmp : Measurable (π.prob (a, s)) := by
    simpa [Measure.prob] using
      Measure.measurable_rnDeriv (π.map (a, s)) ReferenceMeasure.measure
  have hmc : Measurable (π.condProb (a, s)) := by
    change Measurable
      (fun z : α × β ↦
        π.prob (a, s) z /
          (π.map (fun ω ↦ ((a, s) ω).2)).rnDeriv ReferenceMeasure.measure z.2)
    exact hmp.div
      ((Measure.measurable_rnDeriv (π.map (fun ω ↦ ((a, s) ω).2))
        ReferenceMeasure.measure).comp measurable_snd)
  have hd : (fun z : α × β ↦ π.prob (a, s) z) =ᵐ[μα.prod νβ] p := by
    show (π.map (a, s)).rnDeriv (μα.prod νβ) =ᵐ[μα.prod νβ] p
    rw [hjoint]
    exact Measure.rnDeriv_withDensity (μα.prod νβ) hp
  have hm : π.prob s =ᵐ[νβ] q := by
    show (π.map s).rnDeriv νβ =ᵐ[νβ] q
    rw [hlaw]
    exact Measure.rnDeriv_withDensity νβ hq
  have hmd : (fun z : α × β ↦ π.prob s z.2) =ᵐ[μα.prod νβ] fun z ↦ q z.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hm
  have hfactor := All_Eq_MulProbCond.of.PSpace_Joint hP
  have hmy2 : Measurable (π.prob s) :=
    Measure.measurable_rnDeriv (π.map s) νβ
  have hfactor_ms : MeasurableSet
    {z : α × β | π.prob (a, s) z = π.condProb (a, s) z * π.prob s z.2} :=
    measurableSet_eq_fun hmp (hmc.mul (hmy2.comp measurable_snd))
  have hfactor' :
    ∀ᵐ z ∂(μα.prod νβ),
        π.prob (a, s) z = π.condProb (a, s) z * π.prob s z.2 :=
    (Measure.ae_prod_iff_ae_ae hfactor_ms).mpr hfactor
  have hcancel :
    ∀ᵐ z ∂(μα.prod νβ), π.condProb (a, s) z * q z.2 = p z := by
    filter_upwards [hfactor', hd, hmd] with z hf hpz hqz
    rw [← hpz, ← hqz, hf]
  have hswap_eq :
    ∀ᵐ z ∂(νβ.prod μα), π.condProb (a, s) z.swap * q z.1 = p z.swap := by
    have hms : MeasurableSet
      {z : β × α | π.condProb (a, s) z.swap * q z.1 = p z.swap} :=
      measurableSet_eq_fun
        ((hmc.comp measurable_swap).mul (hq.comp measurable_fst))
        (hp.comp measurable_swap)
    have hmap_eq :
      (μα.prod νβ).map Prod.swap = νβ.prod μα :=
      (Measure.measurePreserving_swap (μ := μα) (ν := νβ)).map_eq
    rw [← hmap_eq, MeasureTheory.ae_map_iff measurable_swap.aemeasurable hms]
    simpa [Prod.swap_swap] using hcancel
  have hcond_g :
    ∀ᵐ s0 ∂νβ,
        q s0 ≠ 0 → q s0 ≠ ⊤ →
          ((fun a0 ↦ g s0 a0) =ᵐ[μα]
            fun a0 ↦ π.condProb (a, s) (a0, s0)) ∧
          (∀ᵐ a0 ∂μα, π.condProb (a, s) (a0, s0) < ⊤) := by
    have hpt := Measure.ae_ae_of_ae_prod (μ := νβ) (ν := μα) hswap_eq
    have hptop_ae := Measure.ae_ae_of_ae_prod (μ := νβ) (ν := μα) hptop
    filter_upwards [hpt, hptop_ae] with s0 hpt0 hptop0 hpos hne
    have hlt_p : ∀ᵐ a0 ∂μα, p (a0, s0) ≠ ⊤ :=
      hptop0.mono fun _ h ↦ h hne
    have heq : (fun a0 ↦ g s0 a0) =ᵐ[μα]
      fun a0 ↦ π.condProb (a, s) (a0, s0) := by
      filter_upwards [hpt0, hlt_p] with a0 hmul hpne
      have : g s0 a0 = p (a0, s0) / q s0 := by
        simp [g, hpos, hne, hpne]
      rw [this]
      refine ((ENNReal.eq_div_iff hpos hne).mpr ?_).symm
      rw [mul_comm]
      simpa [Prod.swap] using hmul
    refine ⟨heq, ?_⟩
    filter_upwards [heq] with a0 hg0
    rw [← hg0]
    exact (hg_ne_top s0 a0).lt_top
  have hgood : ∀ᵐ s0 ∂(π.map s),
    q s0 ≠ 0 ∧ q s0 ≠ ⊤ ∧
      ((fun a0 ↦ g s0 a0) =ᵐ[μα]
        fun a0 ↦ π.condProb (a, s) (a0, s0)) ∧
      (∀ᵐ a0 ∂μα, π.condProb (a, s) (a0, s0) < ⊤) := by
    rw [hlaw]
    refine (ae_withDensity_iff hq).mpr ?_
    filter_upwards [hcond_g, hfin] with s0 hg0 hfin0 hpos
    have hne : q s0 ≠ ⊤ := hfin0.ne
    exact ⟨hpos, hne, hg0 hpos hne⟩
  filter_upwards [hκ, hgood] with s0 hκs hgood0
  obtain ⟨hpos, hne, hge, hlt⟩ := hgood0
  have hκs0 :
    κ s0 = μα.withDensity fun a0 ↦ π.condProb (a, s) (a0, s0) := by
    rw [Kernel.withDensity_apply _ hg' s0, Kernel.const_apply]
    exact withDensity_congr_ae hge
  simp only [Expectation.asRV_function, Expectation.condEval]
  rw [hκs, hκs0]
  simpa [Expectation.condRV] using
    ExpectCond.eq.Integral_Mul_ProbCond hP hf s0 hlt


-- created on 2023-03-24
