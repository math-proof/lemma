import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import sympy.stats.joint_rv
import Lemma.Random.All_Eq_MulProbCond.of.PSpace_Joint
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
open ProbabilityTheory MeasureTheory Random


/-- Under counting references, measurability of x, z yields PSpace (x, z). -/
private lemma of_xz
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α} {z : Ω → γ}
-- given
  (hx : Measurable x) (hz : Measurable z)
  (hμα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hμγ : ReferenceMeasure.measure (α := γ) = Measure.count) :
-- imply
  PSpace π (x, z) := by
-- proof
  have hxz_m : AEMeasurable (x, z) π := (hx.prodMk hz).aemeasurable
  have href : (ReferenceMeasure.measure : Measure (α × γ)) =
      (Measure.count (α := α)).prod (Measure.count (α := γ)) := by
    change (ReferenceMeasure.measure (α := α)).prod (ReferenceMeasure.measure (α := γ)) = _
    exact hμα ▸ hμγ ▸ rfl
  have hacc : π.map (x, z) ≪ ReferenceMeasure.measure := by
    rw [href]
    intro s hs0
    have hs_empty : s = (∅ : Set (α × γ)) := by
      refine Set.eq_empty_of_forall_notMem fun ac hac => ?_
      have hle :
          ((Measure.count (α := α)).prod (Measure.count (α := γ))) {ac} ≤
            ((Measure.count (α := α)).prod (Measure.count (α := γ))) s :=
        measure_mono (Set.singleton_subset_iff.mpr hac)
      have h1 :
          ((Measure.count (α := α)).prod (Measure.count (α := γ))) {ac} = 1 := by
        have hset : ({ac} : Set (α × γ)) = {ac.1} ×ˢ {ac.2} := by
          ext; simp [Prod.ext_iff]
        rw [hset, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, mul_one]
      rw [h1, hs0] at hle
      exact absurd hle (by norm_num)
    simp [hs_empty]
  let q : α × γ → ENNReal := (π.map (x, z)).rnDeriv ReferenceMeasure.measure
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hlaw : π.map (x, z) = ReferenceMeasure.measure.withDensity q :=
    (Measure.withDensity_rnDeriv_eq _ _ hacc).symm
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hxz_m
    exists_distribution := ⟨q, ⟨hq⟩, hlaw⟩
  }

@[main]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  [StandardBorelSpace α] [Nonempty α] [Countable α] [MeasurableSingletonClass α]
  [StandardBorelSpace β] [Nonempty β] [Countable β] [MeasurableSingletonClass β]
  [Countable γ] [MeasurableSingletonClass γ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
  (hPxyz : PSpace π (x, y, z))
  (hμα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hμβ : ReferenceMeasure.measure (α := β) = Measure.count)
  (hμγ : ReferenceMeasure.measure (α := γ) = Measure.count)
  (hCI : x ⟂ᵢ[π] y | z) :
-- imply
  have _hPyz : PSpace π (y, z) := PSpace.of.PSpace_Joint.snd hPxyz
  have _hPz : PSpace π z := PSpace.of.PSpace_Joint.snd _hPyz
  have _hPxz : PSpace π (x, z) := of_xz hx hz hμα hμγ
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
    ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
      ∀ᵐ «z.bvar» ∂ReferenceMeasure.measure,
        ℙ[π](y = «y.bvar» ∧ z = «z.bvar») ≠ 0 →
          ℙ[π](x = «x.bvar» | y = «y.bvar» ∧ z = «z.bvar») =
            ℙ[π](x = «x.bvar» | z = «z.bvar») := by
-- proof
  have hPyz : PSpace π (y, z) := PSpace.of.PSpace_Joint.snd hPxyz
  have hPz : PSpace π z := PSpace.of.PSpace_Joint.snd hPyz
  have hPxz : PSpace π (x, z) := of_xz hx hz hμα hμγ
  have hDens :
      ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure,
        ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
          ∀ᵐ «z.bvar» ∂ReferenceMeasure.measure,
            ℙ[π](x = «x.bvar» ∧ y = «y.bvar» ∧ z = «z.bvar») * ℙ[π](z = «z.bvar») =
              ℙ[π](x = «x.bvar» ∧ z = «z.bvar») * ℙ[π](y = «y.bvar» ∧ z = «z.bvar») := by
    rw [hμα, hμβ, hμγ]
    refine ae_of_all _ fun a ↦ ae_of_all _ fun b ↦ ae_of_all _ fun c ↦ ?_
    have hmap :
        π.map (fun ω ↦ (x ω, y ω, z ω)) {(a, b, c)} * π.map z {c} =
          π.map (fun ω ↦ (x ω, z ω)) {(a, c)} * π.map (fun ω ↦ (y ω, z ω)) {(b, c)} := by
      have h_cd :
          condDistrib x (fun ω ↦ (z ω, y ω)) π =ᵐ[π.map (fun ω ↦ (z ω, y ω))]
            (condDistrib x z π).prodMkRight β :=
        (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight (μ := π) hx hy hz).1 hCI.symm
      have h_dis :
          π.map (fun ω ↦ ((z ω, y ω), x ω)) =
            π.map (fun ω ↦ (z ω, y ω)) ⊗ₘ (condDistrib x z π).prodMkRight β := by
        have h0 :
            π.map (fun ω ↦ ((z ω, y ω), x ω)) =
              π.map (fun ω ↦ (z ω, y ω)) ⊗ₘ condDistrib x (fun ω ↦ (z ω, y ω)) π :=
          (compProd_map_condDistrib (Y := x) (X := fun ω ↦ (z ω, y ω)) (μ := π)
            hx.aemeasurable).symm
        rw [h0]
        exact Measure.compProd_congr h_cd
      have h_dis_zx :
          π.map (fun ω ↦ (z ω, x ω)) = π.map z ⊗ₘ condDistrib x z π :=
        (compProd_map_condDistrib (Y := x) (X := z) (μ := π) hx.aemeasurable).symm
      have h_xyz_zyx :
          π.map (fun ω ↦ (x ω, y ω, z ω)) {(a, b, c)} =
            π.map (fun ω ↦ ((z ω, y ω), x ω)) {((c, b), a)} := by
        let f : α × β × γ → (γ × β) × α := fun p ↦ ((p.2.2, p.2.1), p.1)
        have hf : Measurable f := by fun_prop
        have h :
            π.map (fun ω ↦ ((z ω, y ω), x ω)) =
              (π.map (fun ω ↦ (x ω, y ω, z ω))).map f := by
          rw [Measure.map_map hf (by fun_prop)]; rfl
        have hpre : f ⁻¹' {((c, b), a)} = ({(a, b, c)} : Set (α × β × γ)) := by
          ext ⟨x', y', z'⟩
          simp [f, and_comm]
        calc
          π.map (fun ω ↦ (x ω, y ω, z ω)) {(a, b, c)}
              = π.map (fun ω ↦ (x ω, y ω, z ω)) (f ⁻¹' {((c, b), a)}) := by rw [← hpre]
          _ = (π.map (fun ω ↦ (x ω, y ω, z ω))).map f {((c, b), a)} := by
                rw [← Measure.map_apply hf (MeasurableSet.singleton _)]
          _ = π.map (fun ω ↦ ((z ω, y ω), x ω)) {((c, b), a)} := by rw [← h]
      have h_xz_zx :
          π.map (fun ω ↦ (x ω, z ω)) {(a, c)} =
            π.map (fun ω ↦ (z ω, x ω)) {(c, a)} := by
        have h :
            π.map (fun ω ↦ (z ω, x ω)) =
              (π.map (fun ω ↦ (x ω, z ω))).map Prod.swap := by
          rw [Measure.map_map measurable_swap (hx.prodMk hz)]; rfl
        have hpre : Prod.swap ⁻¹' {(c, a)} = ({(a, c)} : Set (α × γ)) := by
          ext ⟨u, v⟩; simp [Prod.swap, and_comm]
        calc
          π.map (fun ω ↦ (x ω, z ω)) {(a, c)}
              = π.map (fun ω ↦ (x ω, z ω)) (Prod.swap ⁻¹' {(c, a)}) := by rw [← hpre]
          _ = (π.map (fun ω ↦ (x ω, z ω))).map Prod.swap {(c, a)} := by
                rw [← Measure.map_apply measurable_swap (MeasurableSet.singleton _)]
          _ = π.map (fun ω ↦ (z ω, x ω)) {(c, a)} := by rw [← h]
      have h_yz_zy :
          π.map (fun ω ↦ (y ω, z ω)) {(b, c)} =
            π.map (fun ω ↦ (z ω, y ω)) {(c, b)} := by
        have h :
            π.map (fun ω ↦ (z ω, y ω)) =
              (π.map (fun ω ↦ (y ω, z ω))).map Prod.swap := by
          rw [Measure.map_map measurable_swap (hy.prodMk hz)]; rfl
        have hpre : Prod.swap ⁻¹' {(c, b)} = ({(b, c)} : Set (β × γ)) := by
          ext ⟨u, v⟩; simp [Prod.swap, and_comm]
        calc
          π.map (fun ω ↦ (y ω, z ω)) {(b, c)}
              = π.map (fun ω ↦ (y ω, z ω)) (Prod.swap ⁻¹' {(c, b)}) := by rw [← hpre]
          _ = (π.map (fun ω ↦ (y ω, z ω))).map Prod.swap {(c, b)} := by
                rw [← Measure.map_apply measurable_swap (MeasurableSet.singleton _)]
          _ = π.map (fun ω ↦ (z ω, y ω)) {(c, b)} := by rw [← h]
      have hL :
          π.map (fun ω ↦ ((z ω, y ω), x ω)) {((c, b), a)} =
            (condDistrib x z π c) {a} * π.map (fun ω ↦ (z ω, y ω)) {(c, b)} := by
        have hset : ({((c, b), a)} : Set ((γ × β) × α)) = {(c, b)} ×ˢ {a} := by
          ext; simp [Prod.ext_iff]
        rw [h_dis, hset,
          Measure.compProd_apply_prod (MeasurableSet.singleton _) (MeasurableSet.singleton _),
          lintegral_singleton]
        simp [Kernel.prodMkRight_apply]
      have hR :
          π.map (fun ω ↦ (z ω, x ω)) {(c, a)} =
            (condDistrib x z π c) {a} * π.map z {c} := by
        have hset : ({(c, a)} : Set (γ × α)) = {c} ×ˢ {a} := by
          ext; simp [Prod.ext_iff]
        rw [h_dis_zx, hset,
          Measure.compProd_apply_prod (MeasurableSet.singleton _) (MeasurableSet.singleton _),
          lintegral_singleton]
      calc
        π.map (fun ω ↦ (x ω, y ω, z ω)) {(a, b, c)} * π.map z {c}
            = π.map (fun ω ↦ ((z ω, y ω), x ω)) {((c, b), a)} * π.map z {c} := by
              rw [h_xyz_zyx]
        _ = ((condDistrib x z π c) {a} * π.map (fun ω ↦ (z ω, y ω)) {(c, b)}) * π.map z {c} := by
              rw [hL]
        _ = ((condDistrib x z π c) {a} * π.map z {c}) * π.map (fun ω ↦ (z ω, y ω)) {(c, b)} := by
              ring
        _ = π.map (fun ω ↦ (z ω, x ω)) {(c, a)} * π.map (fun ω ↦ (z ω, y ω)) {(c, b)} := by
              rw [hR]
        _ = π.map (fun ω ↦ (x ω, z ω)) {(a, c)} * π.map (fun ω ↦ (y ω, z ω)) {(b, c)} := by
              rw [h_xz_zx, h_yz_zy]

    -- Under counting references, `prob` = pushforward singleton mass.
    have hsing_z : π.map z {c} = π.prob z c := by
      have hlaw := PSpace.map_eq_withDensity_density (π := π) (x := z)
      rw [hlaw, show ReferenceMeasure.measure (α := γ) = Measure.count from hμγ,
        withDensity_apply _ (MeasurableSet.singleton _), lintegral_singleton,
        Measure.count_singleton, mul_one]
    have hsing_xz : π.map (x, z) {(a, c)} = π.prob (x, z) (a, c) := by
      have hlaw := PSpace.map_eq_withDensity_density (π := π) (x := (x, z))
      have href : ReferenceMeasure.measure (α := α × γ) =
          (Measure.count (α := α)).prod (Measure.count (α := γ)) := by
        change (ReferenceMeasure.measure (α := α)).prod (ReferenceMeasure.measure (α := γ)) = _
        exact hμα ▸ hμγ ▸ rfl
      rw [hlaw, href, withDensity_apply _ (MeasurableSet.singleton _), lintegral_singleton]
      have : ((Measure.count (α := α)).prod (Measure.count (α := γ))) {(a, c)} = 1 := by
        have hset : ({(a, c)} : Set (α × γ)) = {a} ×ˢ {c} := by
          ext; simp [Prod.ext_iff]
        rw [hset, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, mul_one]
      rw [this, mul_one]
    have hsing_yz : π.map (y, z) {(b, c)} = π.prob (y, z) (b, c) := by
      have hlaw := PSpace.map_eq_withDensity_density (π := π) (x := (y, z))
      have href : ReferenceMeasure.measure (α := β × γ) =
          (Measure.count (α := β)).prod (Measure.count (α := γ)) := by
        change (ReferenceMeasure.measure (α := β)).prod (ReferenceMeasure.measure (α := γ)) = _
        exact hμβ ▸ hμγ ▸ rfl
      rw [hlaw, href, withDensity_apply _ (MeasurableSet.singleton _), lintegral_singleton]
      have : ((Measure.count (α := β)).prod (Measure.count (α := γ))) {(b, c)} = 1 := by
        have hset : ({(b, c)} : Set (β × γ)) = {b} ×ˢ {c} := by
          ext; simp [Prod.ext_iff]
        rw [hset, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, mul_one]
      rw [this, mul_one]
    have hsing_xyz :
        π.map (fun ω ↦ (x ω, y ω, z ω)) {(a, b, c)} = π.prob (x, (y, z)) (a, (b, c)) := by
      have hlaw := PSpace.map_eq_withDensity_density (π := π) (x := (x, (y, z)))
      have href : ReferenceMeasure.measure (α := α × β × γ) =
          (Measure.count (α := α)).prod
            ((Measure.count (α := β)).prod (Measure.count (α := γ))) := by
        change (ReferenceMeasure.measure (α := α)).prod
            ((ReferenceMeasure.measure (α := β)).prod (ReferenceMeasure.measure (α := γ))) = _
        exact hμα ▸ hμβ ▸ hμγ ▸ rfl
      have hflat :
          π.map (fun ω ↦ (x ω, y ω, z ω)) = π.map (x, (y, z)) := by
        rfl
      rw [hflat, hlaw, href, withDensity_apply _ (MeasurableSet.singleton _), lintegral_singleton]
      have : ((Measure.count (α := α)).prod
          ((Measure.count (α := β)).prod (Measure.count (α := γ)))) {(a, (b, c))} = 1 := by
        have hset1 : ({(a, (b, c))} : Set (α × β × γ)) = {a} ×ˢ {(b, c)} := by
          ext; simp [Prod.ext_iff]
        have hset2 : ({(b, c)} : Set (β × γ)) = {b} ×ˢ {c} := by
          ext; simp [Prod.ext_iff]
        rw [hset1, Measure.prod_prod, Measure.count_singleton, hset2, Measure.prod_prod,
          Measure.count_singleton, Measure.count_singleton]; simp
      rw [this, mul_one]
    have hxmap : π.map (fun ω ↦ (x ω, z ω)) = π.map (x, z) := rfl
    have hymap : π.map (fun ω ↦ (y ω, z ω)) = π.map (y, z) := rfl
    have : π.prob (x, (y, z)) (a, (b, c)) * π.prob z c =
        π.prob (x, z) (a, c) * π.prob (y, z) (b, c) := by
      simpa [hsing_xyz.symm, hsing_xz.symm, hsing_yz.symm, hsing_z.symm, hxmap, hymap] using hmap
    simpa using this

  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let ξ : Measure γ := ReferenceMeasure.measure
  have hmul : ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ,
      π.prob (y, z) (b, c) = π.condProb (y, z) (b, c) * π.prob z c :=
    All_Eq_MulProbCond.of.PSpace_Joint hPyz
  have hpyz : Measurable (π.prob (y, z)) := Measure.measurable_rnDeriv _ _
  have hpz : Measurable (π.prob z) := Measure.measurable_rnDeriv _ _
  have hlaw_yz : π.map (y, z) = (ν.prod ξ).withDensity (π.prob (y, z)) :=
    PSpace.map_eq_withDensity_density
  have hlaw_z : π.map z = ξ.withDensity (π.prob z) :=
    PSpace.map_eq_withDensity_density
  have hyz_m : AEMeasurable (y, z) π := hPyz.aemeasurable
  have hz_m : AEMeasurable z π := hPz.aemeasurable
  have htot_yz : ∫⁻ bc, π.prob (y, z) bc ∂(ν.prod ξ) = 1 := by
    have h : ((ν.prod ξ).withDensity (π.prob (y, z))) Set.univ =
        ∫⁻ bc, π.prob (y, z) bc ∂(ν.prod ξ) := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have : IsProbabilityMeasure (π.map (y, z)) :=
      Measure.isProbabilityMeasure_map hyz_m
    rw [← hlaw_yz, measure_univ] at h
    exact h.symm
  have hfin_yz : ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, π.prob (y, z) (b, c) < ⊤ :=
    Measure.ae_ae_of_ae_prod (ae_lt_top hpyz (by rw [htot_yz]; norm_num))
  have htot_z : ∫⁻ c, π.prob z c ∂ξ = 1 := by
    have h : (ξ.withDensity (π.prob z)) Set.univ = ∫⁻ c, π.prob z c ∂ξ := by
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    have : IsProbabilityMeasure (π.map z) :=
      Measure.isProbabilityMeasure_map hz_m
    rw [← hlaw_z, measure_univ] at h
    exact h.symm
  have hfin_z : ∀ᵐ c ∂ξ, π.prob z c < ⊤ :=
    ae_lt_top hpz (by rw [htot_z]; norm_num)
  have hden_yz : π.map (fun ω ↦ ((x, (y, z)) ω).2) = π.map (y, z) := by congr
  have hden_z : π.map (fun ω ↦ ((x, z) ω).2) = π.map z := by congr
  have hmul3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ,
      π.prob (y, z) (b, c) = π.condProb (y, z) (b, c) * π.prob z c := by
    filter_upwards with a
    exact hmul
  have hfin_yz3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, π.prob (y, z) (b, c) < ⊤ := by
    filter_upwards with a
    exact hfin_yz
  have hfin_z3 : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ξ, π.prob z c < ⊤ := by
    filter_upwards with a
    filter_upwards with b
    exact hfin_z
  filter_upwards [hDens, hmul3, hfin_yz3, hfin_z3] with a hDens hmul hfin_yz hfin_z
  filter_upwards [hDens, hmul, hfin_yz, hfin_z] with b hDens hmul hfin_yz hfin_z
  filter_upwards [hDens, hmul, hfin_yz, hfin_z] with c hDens hmul hfin_yz hfin_z
  intro hne
  have hpz_ne : π.prob z c ≠ 0 := by
    intro hz0
    apply hne
    rw [hmul, hz0, mul_zero]
  have hdefL :
      π.condProb (x, (y, z)) (a, (b, c)) =
        π.prob (x, (y, z)) (a, (b, c)) / π.prob (y, z) (b, c) := by
    unfold Measure.condProb Measure.prob
    rw [hden_yz]
  have hdefR :
      π.condProb (x, z) (a, c) =
        π.prob (x, z) (a, c) / π.prob z c := by
    unfold Measure.condProb Measure.prob
    rw [hden_z]
  rw [hdefL, hdefR]
  refine (ENNReal.div_eq_div_iff hpz_ne hfin_z.ne hne hfin_yz.ne).2 ?_
  simpa [mul_comm (π.prob z c), mul_comm (π.prob (y, z) (b, c))] using hDens

-- created on 2026-09-21
-- updated on 2026-09-21
