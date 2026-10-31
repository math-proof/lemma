import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Def.Probability.ChiSquare
import Def.Probability.Fisher
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Real Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 800000


/-- Algebra: `fisherOfBeta d_x d_y (u/(u+v)) = (u/d_x)/(v/d_y)` for positive `u,v`. -/
private lemma fisherOfBeta_div_add
  [NeZero (d_x : ℕ)]
  [NeZero (d_y : ℕ)]
  {u v : ℝ}
  (hu : 0 < u)
  (hv : 0 < v) :
  fisherOfBeta d_x d_y (u / (u + v)) = (u / (d_x : ℝ)) / (v / (d_y : ℝ)) := by
  have hne : (u + v : ℝ) ≠ 0 := ne_of_gt (add_pos hu hv)
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hd1ne : (d_x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d_x)
  have hd2ne : (d_y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d_y)
  have h1 : (1 : ℝ) - u / (u + v) = v / (u + v) := by
    field_simp [hne]
    ring
  unfold fisherOfBeta
  rw [h1]
  have hquot : (u / (u + v)) / (v / (u + v)) = u / v := by
    field_simp [hne, hvne]
  rw [hquot]
  field_simp [hd1ne, hd2ne, hvne]

/-- `Real.chiSquare n` unfolds to `gammaMeasure (n/2) (1/2)` when `n ≠ 0`. -/
private lemma chiSquare_eq_gammaMeasure
  [NeZero (n : ℕ)] :
  Real.chiSquare n = gammaMeasure ((n : ℝ) / 2) (1 / 2) := by
  simp [Real.chiSquare, NeZero.ne n]

/-- Almost every sample of a gamma measure is strictly positive. -/
private lemma gammaMeasure_ae_pos
  {a r : ℝ} :
  ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬0 < x} = Iic (0 : ℝ) := by
    ext x; simp [not_lt]
  rw [hset]
  simp only [gammaMeasure]
  rw [withDensity_apply _ measurableSet_Iic]
  have h :
    (fun x ↦ gammaPDF a r x) =ᵐ[volume.restrict (Iic (0 : ℝ))] 0 := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Iic]
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x hx hxIic
    have hx0 : x ≠ 0 := hx
    have : x < 0 := lt_of_le_of_ne hxIic hx0
    exact gammaPDF_of_neg this
  rw [lintegral_congr_ae h]; simp

/-- Product of two gamma measures is a.e. supported on `(0,∞) × (0,∞)`. -/
private lemma gammaMeasure_prod_ae_pos
  {a b r : ℝ}
  (ha : 0 < a)
  (hb : 0 < b)
  (hr : 0 < r) :
  ∀ᵐ p : ℝ × ℝ ∂(gammaMeasure a r).prod (gammaMeasure b r), 0 < p.1 ∧ 0 < p.2 := by
  have : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  have hmeas :
    MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} :=
    (measurable_fst (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))).inter
      (measurable_snd (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))))
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  filter_upwards [gammaMeasure_ae_pos (a := a) (r := r)] with x hx
  filter_upwards [gammaMeasure_ae_pos (a := b) (r := r)] with y hy
  exact ⟨hx, hy⟩

/-! ### Change of variables `(u,v) ↔ (w,s) = (u/(u+v), u+v)` -/

/-- Open partial homeomorphism for the classical Gamma→Beta change of variables. -/
private noncomputable def gammaBetaCoord : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun q := (q.1 / (q.1 + q.2), q.1 + q.2)
  invFun p := (p.1 * p.2, (1 - p.1) * p.2)
  source := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  target := Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
  map_target' := by
    rintro ⟨w, s⟩ ⟨hw, hs⟩
    exact ⟨mul_pos hw.1 hs, mul_pos (sub_pos.mpr hw.2) hs⟩
  map_source' := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact div_pos hu' (add_pos hu' hv')
    · exact (div_lt_one (add_pos hu' hv')).mpr (lt_add_of_pos_right _ hv')
    · exact add_pos hu' hv'
  left_inv' := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    have hne : (u + v : ℝ) ≠ 0 := ne_of_gt (add_pos hu' hv')
    ext
    · field_simp [hne]
    ·
      field_simp [hne]
      ring
  right_inv' := by
    rintro ⟨w, s⟩ ⟨hw, hs⟩
    have hs' : 0 < s := hs
    ext
    ·
      field_simp [ne_of_gt hs']
      ring
    · ring
  open_source := isOpen_Ioi.prod isOpen_Ioi
  open_target := isOpen_Ioo.prod isOpen_Ioi
  continuousOn_toFun := by
    apply ContinuousOn.prodMk
    ·
      apply ContinuousOn.div continuousOn_fst (continuousOn_fst.add continuousOn_snd)
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      exact ne_of_gt (add_pos (show 0 < u from hu) (show 0 < v from hv))
    · exact continuousOn_fst.add continuousOn_snd
  continuousOn_invFun := by fun_prop

/-- Derivative of the inverse change of variables `(w,s) ↦ (ws,(1-w)s)`. -/
private noncomputable def fderivGammaBetaCoordSymm (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (-p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

private lemma hasFDerivAt_gammaBetaCoord_symm (p : ℝ × ℝ) :
  HasFDerivAt gammaBetaCoord.symm (fderivGammaBetaCoordSymm p) p := by
  have h1 : HasFDerivAt (Prod.fst * Prod.snd : ℝ × ℝ → ℝ)
    (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst.mul hasFDerivAt_snd
  have h2 : HasFDerivAt (((fun _ : ℝ × ℝ ↦ (1 : ℝ)) - Prod.fst) * Prod.snd)
      ((1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
        p.2 • (-ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have h2' : HasFDerivAt (((fun _ : ℝ × ℝ ↦ (1 : ℝ)) - Prod.fst) * Prod.snd)
        ((1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ +
          p.2 • ((0 : ℝ × ℝ →L[ℝ] ℝ) - ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
      ((hasFDerivAt_const (1 : ℝ) p).sub hasFDerivAt_fst).mul hasFDerivAt_snd
    convert h2' using 1
    exact ContinuousLinearMap.ext fun x => by
      simp [add_apply, smul_apply, neg_apply, smul_eq_mul]
  have hprod := HasFDerivAt.prodMk (𝕜 := ℝ) h1 h2
  unfold fderivGammaBetaCoordSymm
  have hL :
    (p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ :
        ℝ × ℝ →L[ℝ] ℝ) =
      p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ :=
    ContinuousLinearMap.ext fun x => by
      simp [add_apply, smul_apply, smul_eq_mul]
      ring
  have hR :
    (-p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ :
        ℝ × ℝ →L[ℝ] ℝ) =
      (1 - p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • (-ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    ContinuousLinearMap.ext fun x => by
      simp [add_apply, smul_apply, neg_apply, smul_eq_mul]
      ring
  rw [hL, hR]
  have hfun :
    (fun q : ℝ × ℝ ↦ ((Prod.fst * Prod.snd : ℝ × ℝ → ℝ) q,
        ((((fun _ : ℝ × ℝ ↦ (1 : ℝ)) - Prod.fst) * Prod.snd : ℝ × ℝ → ℝ) q))) =
      gammaBetaCoord.symm := by
    ext q
    · rfl
    · rfl
  rwa [← hfun]

private lemma det_fderivGammaBetaCoordSymm (p : ℝ × ℝ) :
  (fderivGammaBetaCoordSymm p).det = p.2 := by
  unfold fderivGammaBetaCoordSymm
  rw [← Matrix.toLin_finTwoProd_toContinuousLinearMap p.2 p.1 (-p.2) (1 - p.1)]
  simp [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

private lemma gammaMeasure_prod_eq_withDensity
  {a b r : ℝ} :
  (gammaMeasure a r).prod (gammaMeasure b r) =
    (volume : Measure (ℝ × ℝ)).withDensity
      (fun z : ℝ × ℝ ↦ gammaPDF a r z.1 * gammaPDF b r z.2) := by
  simp only [gammaMeasure, Measure.volume_eq_prod]
  exact prod_withDensity
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    ((measurable_gammaPDFReal b r).ennreal_ofReal)

/-- PDF identity: joint gamma density × Jacobian = beta × gamma of the sum. -/
private lemma gammaPDF_mul_jac_eq_beta_mul_gamma
  {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
  {w s : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) :
  gammaPDF a r (w * s) * gammaPDF b r ((1 - w) * s) * ENNReal.ofReal s =
    betaPDF a b w * gammaPDF (a + b) r s := by
  have hw0 : 0 < w := hw.1
  have hw1 : w < 1 := hw.2
  have h1w : 0 < 1 - w := sub_pos.mpr hw1
  have hws : 0 < w * s := mul_pos hw0 hs
  have h1ws : 0 < (1 - w) * s := mul_pos h1w hs
  rw [gammaPDF_of_nonneg hws.le, gammaPDF_of_nonneg h1ws.le, gammaPDF_of_nonneg hs.le,
    betaPDF_of_pos_lt_one hw0 hw1]
  have hGa : 0 < Gamma a := Gamma_pos_of_pos ha
  have hGb : 0 < Gamma b := Gamma_pos_of_pos hb
  have hGab : 0 < Gamma (a + b) := Gamma_pos_of_pos (add_pos ha hb)
  have hbeta_pos : 0 < beta a b := beta_pos ha hb
  have nA : 0 ≤ r ^ a / Gamma a * (w * s) ^ (a - 1) * rexp (-(r * (w * s))) :=
    mul_nonneg (mul_nonneg (div_nonneg (rpow_nonneg hr.le _) hGa.le)
      (rpow_nonneg hws.le _)) (exp_pos _).le
  have nB : 0 ≤ r ^ b / Gamma b * ((1 - w) * s) ^ (b - 1) * rexp (-(r * ((1 - w) * s))) :=
    mul_nonneg (mul_nonneg (div_nonneg (rpow_nonneg hr.le _) hGb.le)
      (rpow_nonneg h1ws.le _)) (exp_pos _).le
  have nAB : 0 ≤
      (r ^ a / Gamma a * (w * s) ^ (a - 1) * rexp (-(r * (w * s)))) *
        (r ^ b / Gamma b * ((1 - w) * s) ^ (b - 1) * rexp (-(r * ((1 - w) * s)))) :=
    mul_nonneg nA nB
  have nβ : 0 ≤ (1 / beta a b) * w ^ (a - 1) * (1 - w) ^ (b - 1) :=
    mul_nonneg (mul_nonneg (one_div_nonneg.mpr hbeta_pos.le) (rpow_nonneg hw0.le _))
      (rpow_nonneg h1w.le _)
  rw [← ENNReal.ofReal_mul nA, ← ENNReal.ofReal_mul nAB, ← ENNReal.ofReal_mul nβ]
  congr 1
  have hrpow_w : (w * s) ^ (a - 1) = w ^ (a - 1) * s ^ (a - 1) :=
    mul_rpow hw0.le hs.le
  have hrpow_1w : ((1 - w) * s) ^ (b - 1) = (1 - w) ^ (b - 1) * s ^ (b - 1) :=
    mul_rpow h1w.le hs.le
  have hexp : rexp (-(r * (w * s))) * rexp (-(r * ((1 - w) * s))) = rexp (-(r * s)) := by
    rw [← exp_add]; congr 1; ring
  have hs_pow_split : s ^ (a - 1) * s ^ (b - 1) * s = s ^ (a + b - 1) := by
    have h1 : s ^ (a - 1) * s ^ (b - 1) = s ^ ((a - 1) + (b - 1)) :=
      (rpow_add hs (a - 1) (b - 1)).symm
    rw [h1]
    have : (a - 1) + (b - 1) = a + b - 2 := by ring
    rw [this]
    have : s = s ^ (1 : ℝ) := by simp
    nth_rw 2 [this]
    rw [← rpow_add hs]
    congr 1; ring
  have hbeta : (1 : ℝ) / beta a b = Gamma (a + b) / (Gamma a * Gamma b) := by
    simp only [beta]
    field_simp [hGa.ne', hGb.ne', hGab.ne']
  have hr_pow : r ^ a * r ^ b = r ^ (a + b) := (rpow_add hr a b).symm
  calc
    _ = r ^ a / Gamma a * r ^ b / Gamma b * (w * s) ^ (a - 1) * ((1 - w) * s) ^ (b - 1) *
        (rexp (-(r * (w * s))) * rexp (-(r * ((1 - w) * s)))) * s := by ring
    _ = r ^ a / Gamma a * r ^ b / Gamma b * (w ^ (a - 1) * s ^ (a - 1)) *
        ((1 - w) ^ (b - 1) * s ^ (b - 1)) * rexp (-(r * s)) * s := by
      rw [hrpow_w, hrpow_1w, hexp]
    _ = (r ^ a * r ^ b) / (Gamma a * Gamma b) * w ^ (a - 1) * (1 - w) ^ (b - 1) *
        (s ^ (a - 1) * s ^ (b - 1) * s) * rexp (-(r * s)) := by ring
    _ = r ^ (a + b) / (Gamma a * Gamma b) * w ^ (a - 1) * (1 - w) ^ (b - 1) *
        s ^ (a + b - 1) * rexp (-(r * s)) := by
      rw [hr_pow, hs_pow_split]
    _ = (Gamma (a + b) / (Gamma a * Gamma b) * w ^ (a - 1) * (1 - w) ^ (b - 1)) *
        (r ^ (a + b) / Gamma (a + b) * s ^ (a + b - 1) * rexp (-(r * s))) := by
      field_simp [hGa.ne', hGb.ne', hGab.ne']
    _ = ((1 / beta a b) * w ^ (a - 1) * (1 - w) ^ (b - 1)) *
        (r ^ (a + b) / Gamma (a + b) * s ^ (a + b - 1) * rexp (-(r * s))) := by
      rw [hbeta]

/-- The coordinate axes `{0}×ℝ` and `ℝ×{0}` are null for 2-dimensional Lebesgue measure. -/
private lemma volume_axes_eq_zero :
  (volume : Measure (ℝ × ℝ)) ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) = 0 := by
  refine measure_union_null ?_ ?_
  ·
    have : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext; simp [mem_prod]
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  ·
    have : {p : ℝ × ℝ | p.2 = 0} = (univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
      ext; simp [mem_prod]
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]

/-- Joint gamma density vanishes a.e. outside the positive quadrant. -/
private lemma joint_gamma_eq_zero_outside_source_ae {a b r : ℝ} :
  ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
    z ∉ gammaBetaCoord.source → gammaPDF a r z.1 * gammaPDF b r z.2 = 0 := by
  filter_upwards [compl_mem_ae_iff.mpr volume_axes_eq_zero] with z hz hnotin
  have hz' : z.1 ≠ 0 ∧ z.2 ≠ 0 := by
    change ¬(z ∈ {p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}) at hz
    rwa [mem_union, not_or, mem_ofPred_eq, mem_ofPred_eq] at hz
  change ¬(z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) at hnotin
  rw [mem_prod, not_and_or, mem_Ioi, mem_Ioi, not_lt, not_lt] at hnotin
  cases hnotin with
  | inl h =>
    have : z.1 < 0 := lt_of_le_of_ne h hz'.1
    rw [gammaPDF_of_neg this, zero_mul]
  | inr h =>
    have : z.2 < 0 := lt_of_le_of_ne h hz'.2
    rw [gammaPDF_of_neg this, mul_zero]

/-- The gamma density integrates to 1 over `(0,∞)`. -/
private lemma lintegral_gammaPDF_Ioi_eq_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
  ∫⁻ s in Ioi (0 : ℝ), gammaPDF a r s = 1 := by
  have hfull := lintegral_gammaPDF_eq_one ha hr
  have hneg : ∫⁻ x in Iio (0 : ℝ), gammaPDF a r x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio fun x (hx : x < 0) => gammaPDF_of_neg hx,
      lintegral_zero]
  have hIci : ∫⁻ x in Ici (0 : ℝ), gammaPDF a r x = 1 := by
    have h := hfull
    rwa [← lintegral_add_compl _ measurableSet_Ici, compl_Ici, hneg, add_zero] at h
  rwa [setLIntegral_congr (Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]

/-- betaPDF vanishes outside `(0,1)`. -/
private lemma betaPDF_eq_zero_outside_Ioo {α β x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 1) :
  betaPDF α β x = 0 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  cases hx with
  | inl h => exact betaPDF_eq_zero_of_nonpos h
  | inr h => exact betaPDF_eq_zero_of_one_le h

/-- Independent Gamma shapes with common rate: `U/(U+V)` is Beta. -/
private lemma map_div_add_gammaMeasure_eq_betaMeasure
  {a b r : ℝ}
  (ha : 0 < a)
  (hb : 0 < b)
  (hr : 0 < r) :
  ((gammaMeasure a r).prod (gammaMeasure b r)).map
    (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) =
    betaMeasure a b := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [gammaMeasure_prod_eq_withDensity]
  refine Measure.ext fun t ht => ?_
  have hratio : Measurable (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) := by fun_prop
  rw [Measure.map_apply hratio ht, withDensity_apply _ (hratio ht), betaMeasure,
    withDensity_apply _ ht]
  set g : ℝ × ℝ → ℝ≥0∞ := fun z ↦ gammaPDF a r z.1 * gammaPDF b r z.2
  set pre : Set (ℝ × ℝ) := (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) ⁻¹' t
  have hpre : MeasurableSet pre := hratio ht
  -- Restrict integrand to the positive quadrant (full mass of the joint gamma density).
  have hrestrict :
    ∫⁻ z in pre, g z = ∫⁻ z in gammaBetaCoord.source ∩ pre, g z := by
    have hInd :
      (pre.indicator g) =ᵐ[volume]
        ((gammaBetaCoord.source ∩ pre).indicator g) := by
      filter_upwards [joint_gamma_eq_zero_outside_source_ae (a := a) (b := b) (r := r)] with z hz
      if hsrc : z ∈ gammaBetaCoord.source then
        if hp : z ∈ pre then
          simp [hsrc, hp, indicator_of_mem, mem_inter_iff]
        else
          simp [hsrc, hp, indicator_of_notMem, mem_inter_iff]
      else
        have hg0 : g z = 0 := hz hsrc
        if hp : z ∈ pre then
          simp [hsrc, hp, hg0, indicator_of_mem, indicator_of_notMem, mem_inter_iff]
        else
          simp [hsrc, hp, indicator_of_notMem, mem_inter_iff]
    calc
      _ = ∫⁻ z, pre.indicator g z := (lintegral_indicator hpre g).symm
      _ = ∫⁻ z, (gammaBetaCoord.source ∩ pre).indicator g z := lintegral_congr_ae hInd
      _ = ∫⁻ z in gammaBetaCoord.source ∩ pre, g z :=
        lintegral_indicator (gammaBetaCoord.open_source.measurableSet.inter hpre) g
  -- Identify the domain with the image of the target under the inverse CoV map.
  have himg :
    gammaBetaCoord.source ∩ pre =
      gammaBetaCoord.symm '' (gammaBetaCoord.target ∩ Prod.fst ⁻¹' t) := by
    ext p
    constructor
    ·
      intro ⟨hsrc, hpre'⟩
      refine ⟨gammaBetaCoord p, ⟨?_, ?_⟩, ?_⟩
      · exact gammaBetaCoord.map_source hsrc
      ·
        change (p.1 / (p.1 + p.2)) ∈ t
        simpa [pre, mem_preimage] using hpre'
      · exact gammaBetaCoord.left_inv hsrc
    ·
      rintro ⟨q, ⟨hq, hqt⟩, rfl⟩
      refine ⟨gammaBetaCoord.map_target hq, ?_⟩
      have hratio_symm :
        (gammaBetaCoord.symm q).1 / ((gammaBetaCoord.symm q).1 + (gammaBetaCoord.symm q).2) =
          q.1 := by
        have := congrArg Prod.fst (gammaBetaCoord.right_inv hq)
        simpa [gammaBetaCoord] using this
      simpa [pre, mem_preimage, hratio_symm] using hqt
  have hmt : MeasurableSet (gammaBetaCoord.target ∩ Prod.fst ⁻¹' t) :=
    gammaBetaCoord.open_target.measurableSet.inter (measurable_fst ht)
  rw [hrestrict, himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmt
      (fun p _ ↦ (hasFDerivAt_gammaBetaCoord_symm p).hasFDerivWithinAt)
      (gammaBetaCoord.symm.injOn.mono inter_subset_left)]
  -- Replace |det|·g(symm) by the product betaPDF·gammaPDF(a+b).
  have hdens :
    ∀ p ∈ gammaBetaCoord.target ∩ Prod.fst ⁻¹' t,
      ENNReal.ofReal |(fderivGammaBetaCoordSymm p).det| * g (gammaBetaCoord.symm p) =
        betaPDF a b p.1 * gammaPDF (a + b) r p.2 := by
    intro p hp
    have hs : 0 < p.2 := hp.1.2
    rw [det_fderivGammaBetaCoordSymm, abs_of_pos hs]
    have hjac := gammaPDF_mul_jac_eq_beta_mul_gamma ha hb hr hp.1.1 hs
    have hg : g (gammaBetaCoord.symm p) =
        gammaPDF a r (p.1 * p.2) * gammaPDF b r ((1 - p.1) * p.2) := by
      simp only [g, gammaBetaCoord]
      rfl
    rw [hg, mul_comm (ENNReal.ofReal p.2), hjac]
  rw [setLIntegral_congr_fun hmt hdens]
  -- Rewrite the domain as a product set.
  have hset :
    gammaBetaCoord.target ∩ Prod.fst ⁻¹' t =
      (Ioo (0 : ℝ) 1 ∩ t) ×ˢ Ioi (0 : ℝ) := by
    ext p
    change (p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) ∧ p.1 ∈ t) ↔
      (p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.1 ∈ t) ∧ p.2 ∈ Ioi (0 : ℝ)
    simp only [mem_prod, and_assoc, and_left_comm]
    tauto
  rw [hset]
  -- Fubini: product density separates.
  have hfβ : Measurable (betaPDF a b) :=
    (measurable_betaPDFReal a b).ennreal_ofReal
  have hfγ : Measurable (gammaPDF (a + b) r) :=
    (measurable_gammaPDFReal (a + b) r).ennreal_ofReal
  have hFub :
    ∫⁻ p in (Ioo (0 : ℝ) 1 ∩ t) ×ˢ Ioi (0 : ℝ),
        betaPDF a b p.1 * gammaPDF (a + b) r p.2 =
      (∫⁻ w in Ioo (0 : ℝ) 1 ∩ t, betaPDF a b w) *
        (∫⁻ s in Ioi (0 : ℝ), gammaPDF (a + b) r s) := by
    rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), ← Measure.prod_restrict]
    simpa using
      (lintegral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1 ∩ t))
        (ν := volume.restrict (Ioi (0 : ℝ))) hfβ.aemeasurable hfγ.aemeasurable)
  rw [hFub, lintegral_gammaPDF_Ioi_eq_one (add_pos ha hb) hr, mul_one]
  -- betaPDF is supported on (0,1), so restricting the domain to Ioo ∩ t is free.
  refine Eq.symm ?_
  have hInd :
    (t.indicator (betaPDF a b)) =
      ((Ioo (0 : ℝ) 1 ∩ t).indicator (betaPDF a b)) := by
    ext w
    if htw : w ∈ t then
      rw [indicator_of_mem htw]
      if hw : w ∈ Ioo (0 : ℝ) 1 then
        rw [indicator_of_mem (mem_inter hw htw)]
      else
        have hni : w ∉ Ioo (0 : ℝ) 1 ∩ t := fun h ↦ hw h.1
        rw [betaPDF_eq_zero_outside_Ioo hw, indicator_of_notMem hni]
    else
      have hni : w ∉ Ioo (0 : ℝ) 1 ∩ t := fun h ↦ htw h.2
      rw [indicator_of_notMem htw, indicator_of_notMem hni]
  calc
    _ = ∫⁻ w, t.indicator (betaPDF a b) w :=
      (lintegral_indicator ht (betaPDF a b)).symm
    _ = ∫⁻ w, (Ioo (0 : ℝ) 1 ∩ t).indicator (betaPDF a b) w := by rw [hInd]
    _ = ∫⁻ w in Ioo (0 : ℝ) 1 ∩ t, betaPDF a b w :=
      lintegral_indicator (measurableSet_Ioo.inter ht) (betaPDF a b)

private lemma fisherRatio_eq_fisherOfBeta_div_add_ae
  [NeZero (d_x : ℕ)]
  [NeZero (d_y : ℕ)]
  {a b r : ℝ}
  (ha : 0 < a)
  (hb : 0 < b)
  (hr : 0 < r) :
  (fun p : ℝ × ℝ ↦ (p.1 / (d_x : ℝ)) / (p.2 / (d_y : ℝ))) =ᵐ[(gammaMeasure a r).prod (gammaMeasure b r)]
    (fisherOfBeta d_x d_y ∘ fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) := by
  filter_upwards [gammaMeasure_prod_ae_pos ha hb hr] with p hp
  simp only [Function.comp_apply]
  exact (fisherOfBeta_div_add hp.1 hp.2).symm

/--
Characterization: pushforward of independent chi-squareds under the F-ratio
`(u/d_x)/(v/d_y)` equals the Beta-defined Fisher–Snedecor measure `fisherReal`.
-/
@[path]
private lemma main
  [NeZero (d_x : ℕ)]
  [NeZero (d_y : ℕ)] :
-- imply
  fisherReal d_x d_y =
    ((Real.chiSquare d_x).prod (Real.chiSquare d_y)).map
      (fun p : ℝ × ℝ ↦ (p.1 / (d_x : ℝ)) / (p.2 / (d_y : ℝ))) := by
-- proof
  refine Eq.symm ?_
  have ha : 0 < (d_x : ℝ) / 2 := by
    have : (0 : ℕ) < d_x := Nat.pos_of_ne_zero (NeZero.ne d_x)
    positivity
  have hb : 0 < (d_y : ℝ) / 2 := by
    have : (0 : ℕ) < d_y := Nat.pos_of_ne_zero (NeZero.ne d_y)
    positivity
  have hr : (0 : ℝ) < 1 / 2 := by positivity
  rw [chiSquare_eq_gammaMeasure, chiSquare_eq_gammaMeasure]
  have hβ := map_div_add_gammaMeasure_eq_betaMeasure ha hb hr
  have hne : ¬(d_x = 0 ∨ d_y = 0) := by
    intro h
    cases h with
    | inl h1 => exact (NeZero.ne d_x) h1
    | inr h2 => exact (NeZero.ne d_y) h2
  simp only [fisherReal, hne, ↓reduceIte]
  have hm₁ : Measurable (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) := by fun_prop
  have hm₂ : Measurable (fisherOfBeta d_x d_y) := by
    unfold fisherOfBeta
    fun_prop
  rw [← hβ, Measure.map_map hm₂ hm₁]
  refine Measure.map_congr ?_
  exact fisherRatio_eq_fisherOfBeta_div_add_ae ha hb hr


-- created on 2026-10-30
-- updated on 2026-10-31
