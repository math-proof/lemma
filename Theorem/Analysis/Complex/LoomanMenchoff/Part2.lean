/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds
import Def.Analysis.Complex.LoomanMenchoff
/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

theorem looman_exists_boundedAt {f : ℂ → ℂ} {z : ℂ} {r : ℝ} {ax ay : ℂ}
    (hx : HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ))) ax 0)
    (hy : HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ) * Complex.I)) ay 0) :
    ∃ n, loomanBoundedAt f r n z := by
  rcases hx.isBigO_sub.bound with ⟨cx, hcx⟩
  rcases hy.isBigO_sub.bound with ⟨cy, hcy⟩
  rcases Metric.eventually_nhds_iff_ball.mp (hcx.and hcy) with ⟨δ, hδ, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max cx cy) (r / δ))
  refine ⟨n, fun h hh ↦ ?_⟩
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hδh : ‖h‖ < δ := by
    calc
      ‖h‖ < r / (n + 1) := hh
      _ < δ := (div_lt_iff₀ hn1).2 <| by
        calc
          r < (n : ℝ) * δ := (div_lt_iff₀ hδ).1 <|
            lt_of_le_of_lt (le_max_right _ _) hn
          _ < (n + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one (n : ℝ)) hδ
          _ = δ * (n + 1) := mul_comm _ _
  have hb :
      ‖f (z + (h : ℂ)) - f z‖ ≤ cx * ‖h‖ ∧
        ‖f (z + (h : ℂ) * Complex.I) - f z‖ ≤ cy * ‖h‖ := by
    simpa [Real.dist_eq] using hbound h (by simpa [Real.dist_eq] using hδh)
  have hn1' : (n : ℝ) ≤ n + 1 := by linarith
  have hcxn : cx ≤ (n : ℝ) + 1 :=
    le_trans (le_max_left _ _) <| le_trans (le_max_left _ _) <| le_trans hn.le hn1'
  have hcyn : cy ≤ (n : ℝ) + 1 :=
    le_trans (le_max_right _ _) <| le_trans (le_max_left _ _) <| le_trans hn.le hn1'
  constructor
  · exact hb.1.trans <| mul_le_mul_of_nonneg_right hcxn (norm_nonneg h)
  · exact hb.2.trans <| mul_le_mul_of_nonneg_right hcyn (norm_nonneg h)

theorem looman_isClosed_boundedAt {f : ℂ → ℂ} {s C : Set ℂ} {r : ℝ} {n : ℕ}
    (hf : ContinuousOn f s) (hCs : C ⊆ s)
    (hshift : ∀ z ∈ C, ∀ h : ℝ, ‖h‖ < r / (n + 1) →
      z + (h : ℂ) ∈ s ∧ z + (h : ℂ) * Complex.I ∈ s) :
    IsClosed {z : C | loomanBoundedAt f r n z} := by
  have hset : {z : C | loomanBoundedAt f r n z} =
      ⋂ h : ℝ, ⋂ (_ : ‖h‖ < r / (n + 1)),
        {z : C | ‖f (z + (h : ℂ)) - f z‖ ≤ (n + 1) * ‖h‖} ∩
          {z : C | ‖f (z + (h : ℂ) * Complex.I) - f z‖ ≤ (n + 1) * ‖h‖} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, loomanBoundedAt]
  rw [hset]
  apply isClosed_iInter
  intro h
  apply isClosed_iInter
  intro hh
  have hcont : Continuous (fun z : C ↦ f z) :=
    continuousOn_iff_continuous_domRestrict.mp (hf.mono hCs)
  have hcontx : Continuous (fun z : C ↦ f (z + (h : ℂ))) :=
    continuousOn_iff_continuous_domRestrict.mp <|
      hf.comp (by fun_prop) fun z hz ↦ (hshift z hz h hh).1
  have hconty : Continuous (fun z : C ↦ f (z + (h : ℂ) * Complex.I)) :=
    continuousOn_iff_continuous_domRestrict.mp <|
      hf.comp (by fun_prop) fun z hz ↦ (hshift z hz h hh).2
  exact (isClosed_le (hcontx.sub hcont).norm continuous_const).inter
    (isClosed_le (hconty.sub hcont).norm continuous_const)

theorem looman_baire_boundedAt {f : ℂ → ℂ} {s C : Set ℂ} {r : ℝ}
    [BaireSpace C] (hf : ContinuousOn f s) (hCne : C.Nonempty) (hCs : C ⊆ s)
    (hshift : ∀ (n : ℕ) (z : ℂ), z ∈ C → ∀ h : ℝ, ‖h‖ < r / (n + 1) →
      z + (h : ℂ) ∈ s ∧ z + (h : ℂ) * Complex.I ∈ s)
    (hx : ∀ z ∈ C, ∃ a, HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ))) a 0)
    (hy : ∀ z ∈ C, ∃ a, HasDerivAt (fun t : ℝ ↦ f (z + (t : ℂ) * Complex.I)) a 0) :
    ∃ n, (interior {z : C | loomanBoundedAt f r n z}).Nonempty := by
  let A : ℕ → Set C := fun n ↦ {z | loomanBoundedAt f r n z}
  let _ : Nonempty C := hCne.to_subtype
  have hAclosed (n : ℕ) : IsClosed (A n) := looman_isClosed_boundedAt hf hCs (hshift n)
  have hAuniv : ⋃ n, A n = Set.univ := by
    apply Set.eq_univ_of_forall
    rintro ⟨z, hz⟩
    rcases hx z hz with ⟨ax, hax⟩
    rcases hy z hz with ⟨ay, hay⟩
    rcases looman_exists_boundedAt hax hay with ⟨n, hn⟩
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  simpa [A] using nonempty_interior_of_iUnion_of_closed hAclosed hAuniv

theorem looman_oneDimensional_estimate
    {w : ℝ → ℝ} {F : Set ℝ} {a b : ℝ} {K : NNReal}
    (hab : a ≤ b) (hFclosed : IsClosed F) (hFne : F.Nonempty)
    (hF : F ⊆ Icc a b)
    (hdiff : ∀ x ∈ F, DifferentiableAt ℝ w x)
    (hLip : ∀ x ∈ F, ∀ y ∈ Icc a b,
      dist (w x) (w y) ≤ K * dist x y) :
    |w b - w a - ∫ x in F, deriv w x| ≤
      K * (volume (Icc a b \ F)).toReal := by
  obtain ⟨c, hcF⟩ := hFne
  have hc := hF hcF
  let F' := F ∪ {a, b}
  have habLip : dist (w a) (w b) ≤ K * dist a b := by
    calc
      dist (w a) (w b) ≤ dist (w a) (w c) + dist (w c) (w b) := dist_triangle _ _ _
      _ ≤ K * dist a c + K * dist c b := by
        gcongr
        · simpa [dist_comm] using hLip c hcF a ⟨le_rfl, hab⟩
        · exact hLip c hcF b ⟨hab, le_rfl⟩
      _ = K * dist a b := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hc.1),
          abs_of_nonpos (sub_nonpos.2 hc.2), abs_of_nonpos (sub_nonpos.2 hab)]
        ring
  have hLip' : LipschitzOnWith K w F' := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [F', mem_union, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hLip x hx y (hF hy)
    · rcases hy with hya | hyb
      · subst y
        exact hLip x hx a ⟨le_rfl, hab⟩
      · subst y
        exact hLip x hx b ⟨hab, le_rfl⟩
    · rcases hx with hxa | hxb
      · subst x
        simpa [dist_comm] using hLip y hy a ⟨le_rfl, hab⟩
      · subst x
        simpa [dist_comm] using hLip y hy b ⟨hab, le_rfl⟩
    · rcases hx with hxa | hxb <;> rcases hy with hya | hyb
      · subst x; subst y; simp
      · subst x; subst y; exact habLip
      · subst x; subst y; simpa [dist_comm] using habLip
      · subst x; subst y; simp
  obtain ⟨g, hgLip, hwg⟩ := hLip'.extend_real
  have hga : g a = w a := (hwg (by simp [F'])).symm
  have hgb : g b = w b := (hwg (by simp [F'])).symm
  have hgAC : AbsolutelyContinuousOnInterval g a b := by
    apply hgLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hderiv : ∀ᵐ x ∂volume.restrict F, deriv g x = deriv w x := by
    have hcount : {x | x ∈ F ∧ nhdsWithin x (F ∩ Ioi x) = ⊥}.Countable :=
      countable_setOfPred_isolated_right_within
    apply (ae_restrict_iff' hFclosed.measurableSet).2
    filter_upwards [hgLip.ae_differentiableAt_real,
      measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero volume)] with x hgdiff hxnot hxF
    have huniq : UniqueDiffWithinAt ℝ F x := by
      rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin]
      have hnb : (nhdsWithin x (F ∩ Ioi x)).NeBot := by
        rw [neBot_iff]
        exact fun hbot ↦ hxnot ⟨hxF, hbot⟩
      exact hnb.mono (nhdsWithin_mono x fun y hy ↦
        ⟨hy.1, fun h ↦ by subst y; exact (lt_irrefl x) hy.2⟩)
    exact huniq.eq_deriv F
      (hgdiff.hasDerivAt.hasDerivWithinAt.congr
        (fun y hy ↦ hwg (by exact Or.inl hy)) (hwg (by exact Or.inl hxF)))
      ((hdiff x hxF).hasDerivAt.hasDerivWithinAt)
  have hgInt : IntegrableOn (deriv g) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hgAC.intervalIntegrable_deriv
  have hgFInt : IntegrableOn (deriv g) F := hgInt.mono_set hF
  have hwFInt : IntegrableOn (deriv w) F := by
    apply hgFInt.congr
    filter_upwards [hderiv] with x hx
    simpa using hx
  have hdecomp := integral_inter_add_sdiff hFclosed.measurableSet hgInt
  have hinter : Icc a b ∩ F = F := inter_eq_right.2 hF
  rw [hinter] at hdecomp
  have hFTC : ∫ x in Icc a b, deriv g x = g b - g a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact hgAC.integral_deriv_eq_sub
  have hFg : (∫ x in F, deriv g x) = ∫ x in F, deriv w x :=
    integral_congr_ae hderiv
  have hrem : w b - w a - ∫ x in F, deriv w x =
      ∫ x in Icc a b \ F, deriv g x := by
    rw [← hFg, ← hga, ← hgb, ← hFTC, ← hdecomp]
    ring
  rw [hrem]
  simpa only [Real.norm_eq_abs, measureReal_def] using
    (norm_setIntegral_le_of_norm_le_const_ae
      ((lt_top_iff_ne_top).2 (measure_ne_top_of_subset Set.sdiff_subset (by simp)))
      (ae_of_all _ fun _ ↦ norm_deriv_le_of_lipschitz hgLip) :
      ‖∫ x in Icc a b \ F, deriv g x‖ ≤
        (K : ℝ) * volume.real (Icc a b \ F))

theorem looman_integral_fiber_measureReal {S : Set (ℝ × ℝ)} {c d : ℝ}
    (hS : MeasurableSet S) (hsub : S ⊆ Set.univ ×ˢ Icc c d) :
    ∫ x : ℝ, volume.real (Prod.mk x ⁻¹' S) = (volume.prod volume).real S := by
  rw [measureReal_def, Measure.prod_apply hS]
  rw [← integral_toReal (measurable_measure_prodMk_left hS).aemeasurable]
  · congr 1
  · filter_upwards with x
    exact lt_top_iff_ne_top.2 <| measure_ne_top_of_subset
      (fun y hy ↦ (hsub hy).2) (by simp)

theorem looman_vertical_estimate
    {φ : ℝ × ℝ → ℝ} {E : Set (ℝ × ℝ)}
    {A B C D a b c d K L κ : ℝ}
    (hAa : A ≤ a) (hbB : b ≤ B)
    (hCc : C ≤ c) (hcd : c ≤ d) (hdD : d ≤ D)
    (hCD : C < D)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hLx : B - A ≤ L) (hLy : D - C ≤ L) (hLheight : L ≤ κ * (D - C))
    (hcont : Continuous φ) (hEclosed : IsClosed E) (hEcompact : IsCompact E)
    (hEsub : E ⊆ Icc a b ×ˢ Icc c d)
    (hbot : ∃ x, (x, c) ∈ E) (htop : ∃ x, (x, d) ∈ E)
    (hdiff : ∀ p ∈ E, DifferentiableAt ℝ (fun y ↦ φ (p.1, y)) p.2)
    (hderiv : ∀ p ∈ E, |deriv (fun y ↦ φ (p.1, y)) p.2| ≤ K)
    (hLipX : ∀ p ∈ E, ∀ x ∈ Icc A B,
      |φ (x, p.2) - φ p| ≤ K * |x - p.1|)
    (hLipY : ∀ p ∈ E, ∀ y ∈ Icc C D,
      |φ (p.1, y) - φ p| ≤ K * |y - p.2|) :
    |(∫ x in Icc a b, φ (x, d) - φ (x, c)) -
        ∫ p in E, deriv (fun y ↦ φ (p.1, y)) p.2 ∂(volume.prod volume)| ≤
      (1 + 4 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ E) := by
  let P : Set ℝ := Prod.fst '' E
  have hPcompact : IsCompact P := hEcompact.image continuous_fst
  have hPclosed : IsClosed P := hPcompact.isClosed
  have hPsub : P ⊆ Icc a b := by
    rintro x ⟨p, hpE, rfl⟩
    exact (hEsub hpE).1
  let R : Set (ℝ × ℝ) := Icc A B ×ˢ Icc C D
  let S : Set (ℝ × ℝ) := R \ E
  have hRmeas : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hSmeas : MeasurableSet S := hRmeas.diff hEclosed.measurableSet
  have hSsub : S ⊆ Set.univ ×ˢ Icc C D := by
    intro p hp
    exact ⟨mem_univ _, hp.1.2⟩
  let dy : ℝ × ℝ → ℝ := fun p ↦ deriv (fun y ↦ φ (p.1, y)) p.2
  have hdymeas : Measurable dy := by
    exact measurable_deriv_with_param (f := fun x y ↦ φ (x, y)) (by
      change Continuous (fun p : ℝ × ℝ ↦ φ p)
      exact hcont)
  have hdyInt : IntegrableOn dy E (volume.prod volume) := by
    refine Measure.integrableOn_of_bounded (M := K) hEcompact.measure_lt_top.ne
      hdymeas.aestronglyMeasurable ?_
    exact (ae_restrict_iff' hEclosed.measurableSet).2 <| by
      filter_upwards with p hp
      simpa [dy, Real.norm_eq_abs] using hderiv p hp
  let G : ℝ × ℝ → ℝ := E.indicator dy
  have hGInt : Integrable G (volume.prod volume) :=
    hdyInt.integrable_indicator hEclosed.measurableSet
  let q : ℝ → ℝ := fun x ↦ ∫ y : ℝ, G (x, y)
  have hqInt : Integrable q volume := hGInt.integral_prod_left
  have hEIntegral : (∫ p in E, dy p ∂(volume.prod volume)) = ∫ x, q x := by
    rw [← integral_indicator hEclosed.measurableSet, integral_prod _ hGInt]
  have hq_zero {x : ℝ} (hx : x ∉ P) : q x = 0 := by
    simp only [q]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    have hxy : (x, y) ∉ E := fun h ↦ hx ⟨(x, y), h, rfl⟩
    simp [G, hxy]
  have hqIntegralP : (∫ x, q x) = ∫ x in P, q x := by
    rw [← integral_indicator hPclosed.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ P
    · simp [hx]
    · simp [hx, hq_zero hx]
  let v : ℝ → ℝ := fun x ↦ φ (x, d) - φ (x, c)
  have hvcont : Continuous v := by
    dsimp [v]
    fun_prop
  have hvInt : IntegrableOn v (Icc a b) volume :=
    hvcont.continuousOn.integrableOn_compact isCompact_Icc
  have hqPInt : IntegrableOn q P volume := hqInt.integrableOn
  let e : ℝ → ℝ := fun x ↦ v x - q x
  have hePInt : IntegrableOn e P volume :=
    (hvInt.mono_set hPsub).sub hqPInt
  let T : Set ℝ := Icc a b \ P
  have hTmeas : MeasurableSet T := measurableSet_Icc.diff hPclosed.measurableSet
  have hvTInt : IntegrableOn v T volume := hvInt.mono_set Set.sdiff_subset
  have hdecomp : (∫ x in Icc a b, v x) - ∫ x, q x =
      (∫ x in P, e x) + ∫ x in T, v x := by
    have hsplit := integral_inter_add_sdiff hPclosed.measurableSet hvInt
    rw [inter_eq_right.2 hPsub] at hsplit
    rw [hqIntegralP, ← hsplit]
    rw [integral_sub (hvInt.mono_set hPsub) hqPInt]
    ring
  let m : ℝ → ℝ := fun x ↦ volume.real (Prod.mk x ⁻¹' S)
  have hmmeas : Measurable m := (measurable_measure_prodMk_left hSmeas).ennreal_toReal
  have hm_nonneg (x : ℝ) : 0 ≤ m x := measureReal_nonneg
  have hm_zero {x : ℝ} (hx : x ∉ Icc A B) : m x = 0 := by
    change volume.real (Prod.mk x ⁻¹' S) = 0
    rw [show Prod.mk x ⁻¹' S = ∅ by
      ext y
      simp only [Set.mem_preimage, mem_empty_iff_false, iff_false]
      intro hy
      exact hx hy.1.1]
    simp
  have hm_bound (x : ℝ) : m x ≤ D - C := by
    change volume.real (Prod.mk x ⁻¹' S) ≤ D - C
    rw [measureReal_def]
    have hvol : D - C = (volume (Icc C D)).toReal := by simp [hCD.le]
    rw [hvol]
    apply ENNReal.toReal_mono (by simp)
    exact measure_mono fun y hy ↦ (hSsub hy).2
  have hmInt : Integrable m volume := by
    have hi : IntegrableOn m (Icc A B) volume := by
      refine Measure.integrableOn_of_bounded (M := D - C) (by simp)
        hmmeas.aestronglyMeasurable ?_
      exact (ae_restrict_iff' measurableSet_Icc).2 <| by
        filter_upwards with x _
        rw [Real.norm_eq_abs, abs_of_nonneg (hm_nonneg x)]
        exact hm_bound x
    apply (hi.integrable_indicator measurableSet_Icc).congr
    filter_upwards with x
    by_cases hx : x ∈ Icc A B
    · simp [hx]
    · simp [hx, hm_zero hx]
  have hmIntegral : (∫ x, m x) = (volume.prod volume).real S := by
    exact looman_integral_fiber_measureReal hSmeas hSsub
  have he_bound : ∀ x ∈ P, |e x| ≤ K * m x := by
    rintro x ⟨p, hpE, rfl⟩
    let Fx : Set ℝ := Prod.mk p.1 ⁻¹' E
    have hFxclosed : IsClosed Fx := hEclosed.preimage (by fun_prop)
    have hFxne : Fx.Nonempty := ⟨p.2, hpE⟩
    have hFxsub : Fx ⊆ Icc c d := fun y hy ↦ (hEsub hy).2
    have hone := looman_oneDimensional_estimate (w := fun y ↦ φ (p.1, y))
      (K := ⟨K, hK⟩) hcd hFxclosed hFxne hFxsub
      (fun y hy ↦ hdiff (p.1, y) hy)
      (fun y hy z hz ↦ by
        change |φ (p.1, y) - φ (p.1, z)| ≤ K * |y - z|
        simpa only [Real.dist_eq, abs_sub_comm] using hLipY (p.1, y) hy z
          ⟨hCc.trans hz.1, hz.2.trans hdD⟩)
    have hqeq : q p.1 = ∫ y in Fx, deriv (fun y ↦ φ (p.1, y)) y := by
      simp only [q]
      rw [← integral_indicator hFxclosed.measurableSet]
      apply integral_congr_ae
      filter_upwards with y
      rfl
    have hsubset : Icc c d \ Fx ⊆ Prod.mk p.1 ⁻¹' S := by
      rintro y ⟨hycd, hyE⟩
      exact ⟨⟨⟨hAa.trans (hEsub hpE).1.1, (hEsub hpE).1.2.trans hbB⟩,
        ⟨hCc.trans hycd.1, hycd.2.trans hdD⟩⟩, hyE⟩
    have hmeasure : (volume (Icc c d \ Fx)).toReal ≤ m p.1 := by
      change volume.real (Icc c d \ Fx) ≤ volume.real (Prod.mk p.1 ⁻¹' S)
      exact measureReal_mono hsubset (h₂ :=
        measure_ne_top_of_subset (fun y hy ↦ (hSsub hy).2) (by simp))
    change |φ (p.1, d) - φ (p.1, c) - q p.1| ≤ K * m p.1
    rw [hqeq]
    have hone' : |φ (p.1, d) - φ (p.1, c) -
        ∫ y in Fx, deriv (fun y ↦ φ (p.1, y)) y| ≤
        K * (volume (Icc c d \ Fx)).toReal := by
      change _ ≤ K * (volume (Icc c d \ Fx)).toReal at hone
      exact hone
    exact hone'.trans (mul_le_mul_of_nonneg_left hmeasure hK)
  have he_norm : ‖∫ x in P, e x‖ ≤ K * (volume.prod volume).real S := by
    calc
      ‖∫ x in P, e x‖ ≤ ∫ x in P, ‖e x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in P, K * m x := by
        exact setIntegral_mono_on hePInt.norm ((hmInt.const_mul K).integrableOn)
          hPclosed.measurableSet fun x hx ↦ by
            simpa [Real.norm_eq_abs] using he_bound x hx
      _ ≤ ∫ x, K * m x := by
        rw [← integral_indicator hPclosed.measurableSet]
        apply integral_mono_ae
          ((hmInt.const_mul K).integrableOn.integrable_indicator hPclosed.measurableSet)
          (hmInt.const_mul K)
        filter_upwards with x
        by_cases hx : x ∈ P
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          exact mul_nonneg hK (hm_nonneg x)
      _ = K * (volume.prod volume).real S := by
        rw [integral_const_mul, hmIntegral]
  obtain ⟨x₀, hx₀⟩ := hbot
  obtain ⟨x₁, hx₁⟩ := htop
  have hx₀ab := (hEsub hx₀).1
  have hx₁ab := (hEsub hx₁).1
  have hv_bound (x : ℝ) (hx : x ∈ Icc a b) : |v x| ≤ 4 * K * L := by
    have h1 := hLipX (x₁, d) hx₁ x ⟨hAa.trans hx.1, hx.2.trans hbB⟩
    have h2 := hLipX (x₁, d) hx₁ x₀ ⟨hAa.trans hx₀ab.1, hx₀ab.2.trans hbB⟩
    have h3 := hLipY (x₀, c) hx₀ d ⟨hCc.trans hcd, hdD⟩
    have h4 := hLipX (x₀, c) hx₀ x ⟨hAa.trans hx.1, hx.2.trans hbB⟩
    have hxL (u v : ℝ) (hu : u ∈ Icc A B) (hv : v ∈ Icc A B) : |u - v| ≤ L := by
      calc
        |u - v| ≤ B - A := by
          rw [abs_le]
          constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
        _ ≤ L := hLx
    have hyL : |d - c| ≤ L := by
      rw [abs_of_nonneg (sub_nonneg.2 hcd)]
      exact (sub_le_sub hdD hCc).trans hLy
    have habs (r s t u : ℝ) : |r + s + t + u| ≤ |r| + |s| + |t| + |u| := by
      linarith [abs_add_le r s, abs_add_le (r + s) t, abs_add_le (r + s + t) u]
    have h1L : |φ (x, d) - φ (x₁, d)| ≤ K * L :=
      h1.trans (mul_le_mul_of_nonneg_left
        (hxL x x₁ ⟨hAa.trans hx.1, hx.2.trans hbB⟩
          ⟨hAa.trans hx₁ab.1, hx₁ab.2.trans hbB⟩) hK)
    have h2L : |φ (x₁, d) - φ (x₀, d)| ≤ K * L := by
      rw [abs_sub_comm]
      exact h2.trans (mul_le_mul_of_nonneg_left
        (hxL x₀ x₁ ⟨hAa.trans hx₀ab.1, hx₀ab.2.trans hbB⟩
          ⟨hAa.trans hx₁ab.1, hx₁ab.2.trans hbB⟩) hK)
    have h3L : |φ (x₀, d) - φ (x₀, c)| ≤ K * L :=
      h3.trans (mul_le_mul_of_nonneg_left hyL hK)
    have h4L : |φ (x₀, c) - φ (x, c)| ≤ K * L := by
      rw [abs_sub_comm]
      exact h4.trans (mul_le_mul_of_nonneg_left
        (hxL x x₀ ⟨hAa.trans hx.1, hx.2.trans hbB⟩
          ⟨hAa.trans hx₀ab.1, hx₀ab.2.trans hbB⟩) hK)
    calc
      |v x| = |(φ (x, d) - φ (x₁, d)) + (φ (x₁, d) - φ (x₀, d)) +
          (φ (x₀, d) - φ (x₀, c)) + (φ (x₀, c) - φ (x, c))| := by
        dsimp [v]
        congr 1
        ring
      _ ≤ |φ (x, d) - φ (x₁, d)| + |φ (x₁, d) - φ (x₀, d)| +
          |φ (x₀, d) - φ (x₀, c)| + |φ (x₀, c) - φ (x, c)| := by
        exact habs _ _ _ _
      _ ≤ K * L + K * L + K * L + K * L := by
        exact add_le_add (add_le_add (add_le_add h1L h2L) h3L) h4L
      _ = 4 * K * L := by ring
  have hTprod : T ×ˢ Icc C D ⊆ S := by
    rintro ⟨x, y⟩ ⟨hxT, hyCD⟩
    refine ⟨⟨?_, hyCD⟩, ?_⟩
    · exact ⟨hAa.trans hxT.1.1, hxT.1.2.trans hbB⟩
    · intro hxyE
      exact hxT.2 ⟨(x, y), hxyE, rfl⟩
  have hstrip : L * volume.real T ≤ κ * (volume.prod volume).real S := by
    have hDClen : volume.real (Icc C D) = D - C := by simp [hCD.le]
    calc
      L * volume.real T ≤ κ * (D - C) * volume.real T :=
        mul_le_mul_of_nonneg_right hLheight measureReal_nonneg
      _ = κ * (volume.prod volume).real (T ×ˢ Icc C D) := by
        rw [measureReal_prod_prod, hDClen]
        ring
      _ ≤ κ * (volume.prod volume).real S := by
        apply mul_le_mul_of_nonneg_left _ hκ
        have hRcompact : IsCompact R := isCompact_Icc.prod isCompact_Icc
        have hSfinite : (volume.prod volume) S ≠ ∞ :=
          measure_ne_top_of_subset Set.sdiff_subset hRcompact.measure_lt_top.ne
        exact measureReal_mono hTprod (h₂ := hSfinite)
  have hv_norm : ‖∫ x in T, v x‖ ≤ 4 * K * κ * (volume.prod volume).real S := by
    calc
      ‖∫ x in T, v x‖ ≤ 4 * K * L * volume.real T := by
        apply norm_setIntegral_le_of_norm_le_const_ae
        · exact (measure_ne_top_of_subset Set.sdiff_subset (by simp)).lt_top
        · apply (ae_restrict_iff' hTmeas).2
          filter_upwards with x hx
          simpa [Real.norm_eq_abs] using hv_bound x hx.1
      _ = 4 * K * (L * volume.real T) := by ring
      _ ≤ 4 * K * (κ * (volume.prod volume).real S) := by gcongr
      _ = 4 * K * κ * (volume.prod volume).real S := by ring
  rw [show (∫ p in E, deriv (fun y ↦ φ (p.1, y)) p.2 ∂(volume.prod volume)) =
      ∫ p in E, dy p ∂(volume.prod volume) by rfl]
  rw [hEIntegral, hdecomp]
  calc
    |(∫ x in P, e x) + ∫ x in T, v x| =
        ‖(∫ x in P, e x) + ∫ x in T, v x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖∫ x in P, e x‖ + ‖∫ x in T, v x‖ := norm_add_le _ _
    _ ≤ K * (volume.prod volume).real S +
        4 * K * κ * (volume.prod volume).real S := add_le_add he_norm hv_norm
    _ = (1 + 4 * κ) * K * (volume.prod volume).real S := by ring
    _ = _ := rfl

theorem looman_horizontal_estimate
    {φ : ℝ × ℝ → ℝ} {E : Set (ℝ × ℝ)}
    {A B C D a b c d K L κ : ℝ}
    (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B)
    (hCc : C ≤ c) (hdD : d ≤ D)
    (hAB : A < B)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hLx : B - A ≤ L) (hLy : D - C ≤ L) (hLwidth : L ≤ κ * (B - A))
    (hcont : Continuous φ) (hEclosed : IsClosed E) (hEcompact : IsCompact E)
    (hEsub : E ⊆ Icc a b ×ˢ Icc c d)
    (hleft : ∃ y, (a, y) ∈ E) (hright : ∃ y, (b, y) ∈ E)
    (hdiff : ∀ p ∈ E, DifferentiableAt ℝ (fun x ↦ φ (x, p.2)) p.1)
    (hderiv : ∀ p ∈ E, |deriv (fun x ↦ φ (x, p.2)) p.1| ≤ K)
    (hLipX : ∀ p ∈ E, ∀ x ∈ Icc A B,
      |φ (x, p.2) - φ p| ≤ K * |x - p.1|)
    (hLipY : ∀ p ∈ E, ∀ y ∈ Icc C D,
      |φ (p.1, y) - φ p| ≤ K * |y - p.2|) :
    |(∫ y in Icc c d, φ (b, y) - φ (a, y)) -
        ∫ p in E, deriv (fun x ↦ φ (x, p.2)) p.1 ∂(volume.prod volume)| ≤
      (1 + 4 * κ) * K * (volume.prod volume).real
        ((Icc A B ×ˢ Icc C D) \ E) := by
  let ψ : ℝ × ℝ → ℝ := fun p ↦ φ p.swap
  let F : Set (ℝ × ℝ) := Prod.swap '' E
  have hFcompact : IsCompact F := hEcompact.image continuous_swap
  have hFclosed : IsClosed F := hFcompact.isClosed
  have hFsub : F ⊆ Icc c d ×ˢ Icc a b := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨(hEsub hq).2, (hEsub hq).1⟩
  have hFbot : ∃ x, (x, a) ∈ F := by
    obtain ⟨y, hy⟩ := hleft
    exact ⟨y, ⟨(a, y), hy, rfl⟩⟩
  have hFtop : ∃ x, (x, b) ∈ F := by
    obtain ⟨y, hy⟩ := hright
    exact ⟨y, ⟨(b, y), hy, rfl⟩⟩
  have hψcont : Continuous ψ := hcont.comp continuous_swap
  have hFdiff : ∀ p ∈ F, DifferentiableAt ℝ (fun y ↦ ψ (p.1, y)) p.2 := by
    rintro p ⟨q, hq, rfl⟩
    simpa [ψ] using hdiff q hq
  have hFderiv : ∀ p ∈ F, |deriv (fun y ↦ ψ (p.1, y)) p.2| ≤ K := by
    rintro p ⟨q, hq, rfl⟩
    simpa [ψ] using hderiv q hq
  have hFLipX : ∀ p ∈ F, ∀ x ∈ Icc C D,
      |ψ (x, p.2) - ψ p| ≤ K * |x - p.1| := by
    rintro p ⟨q, hq, rfl⟩ x hx
    simpa [ψ] using hLipY q hq x hx
  have hFLipY : ∀ p ∈ F, ∀ y ∈ Icc A B,
      |ψ (p.1, y) - ψ p| ≤ K * |y - p.2| := by
    rintro p ⟨q, hq, rfl⟩ y hy
    simpa [ψ] using hLipX q hq y hy
  have h := looman_vertical_estimate (A := C) (B := D) (C := A) (D := B)
    (a := c) (b := d) (c := a) (d := b) (K := K) (L := L) (κ := κ)
    hCc hdD hAa hab hbB hAB hK hκ hLy hLx hLwidth
    hψcont hFclosed hFcompact hFsub hFbot hFtop hFdiff hFderiv hFLipX hFLipY
  have hintergral :
      (∫ p in F, deriv (fun y ↦ ψ (p.1, y)) p.2 ∂(volume.prod volume)) =
        ∫ p in E, deriv (fun x ↦ φ (x, p.2)) p.1 ∂(volume.prod volume) := by
    rw [show F = Prod.swap '' E by rfl]
    rw [(Measure.measurePreserving_swap (μ := volume) (ν := volume)).setIntegral_image_emb
      MeasurableEquiv.prodComm.measurableEmbedding]
    apply setIntegral_congr_fun hEclosed.measurableSet
    intro p hp
    simp [ψ]
  have hsets : (Icc C D ×ˢ Icc A B) \ F =
      Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E) := by
    ext p
    simp only [F, Set.mem_sdiff, mem_prod, Set.mem_Icc, Set.mem_image]
    constructor
    · rintro ⟨hpR, hpF⟩
      refine ⟨p.swap, ⟨⟨hpR.2, hpR.1⟩, ?_⟩, by simp⟩
      intro hpE
      exact hpF ⟨p.swap, hpE, by simp⟩
    · rintro ⟨q, ⟨hqR, hqE⟩, rfl⟩
      refine ⟨⟨hqR.2, hqR.1⟩, ?_⟩
      rintro ⟨r, hrE, hrswap⟩
      have : r = q := by
        apply Prod.swap_injective
        simpa using hrswap
      exact hqE (this ▸ hrE)
  have hmeasure : (volume.prod volume).real ((Icc C D ×ˢ Icc A B) \ F) =
      (volume.prod volume).real ((Icc A B ×ˢ Icc C D) \ E) := by
    rw [hsets, measureReal_def, measureReal_def]
    congr 1
    let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
    let hp := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
    calc
      μ (Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E)) =
          (Measure.map Prod.swap μ) (Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E)) := by
        rw [hp.map_eq]
      _ = μ (Prod.swap ⁻¹' (Prod.swap '' ((Icc A B ×ˢ Icc C D) \ E))) :=
        MeasurableEquiv.prodComm.measurableEmbedding.map_apply _ _
      _ = μ ((Icc A B ×ˢ Icc C D) \ E) := by
        congr 1
        ext p
        simp
  rw [hintergral, hmeasure] at h
  simpa [ψ] using h

end
end MetaMathlibExt
