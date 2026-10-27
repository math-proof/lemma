import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[relative_extremum_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean)
-/
@[path]
lemma relative_extremum_def
  {f : ℝ → ℝ}
  {S : Set ℝ}
  {c : ℝ}
-- given
  (_hc : c ∈ S) :
-- imply
  (IsLocalMaxOn f S c ↔ ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → f x ≤ f c) ∧ (IsLocalMinOn f S c ↔ ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → f c ≤ f x) := by
-- proof
  have key : ∀ (q : ℝ → Prop),
    (∀ᶠ x in nhdsWithin c S, q x) ↔ ∃ δ > 0, ∀ x ∈ S, |x - c| < δ → q x := by
    intro q
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    simp only [Real.dist_eq]
    constructor
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun x hxS hd => h hd hxS⟩
    · rintro ⟨ε, hε, h⟩
      exact ⟨ε, hε, fun x hd hxS => h x hxS hd⟩
  exact ⟨key _, key _⟩

/--
[fermats_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean)
-/
@[path]
lemma fermats_theorem
  {f : ℝ → ℝ}
  {c : ℝ}
-- given
  (hext : IsLocalMax f c ∨ IsLocalMin f c)
  (_hd : DifferentiableAt ℝ f c) :
-- imply
  deriv f c = 0 := by
-- proof
  obtain hmax | hmin := hext
  · exact hmax.deriv_eq_zero
  · exact hmin.deriv_eq_zero

/--
[rolle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean)
-/
@[path]
lemma rolle
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hfc : ContinuousOn f (Set.Icc a b))
  (_hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (heq : f a = f b) :
-- imply
  ∃ c ∈ Set.Ioo a b, deriv f c = 0 :=
-- proof
  exists_deriv_eq_zero hab hfc heq

/--
[mean_value_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean)
-/
@[path]
lemma mean_value_theorem
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hfc : ContinuousOn f (Set.Icc a b))
  (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
-- imply
  ∃ c ∈ Set.Ioo a b, f b - f a = deriv f c * (b - a) := by
-- proof
  have hfd' : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun x hx => (hfd x hx).differentiableWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope f hab hfc hfd'
  have hba : (b - a) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  exact ⟨c, hc, by rw [hc', div_mul_cancel₀ (f b - f a) hba]⟩

/--
[zero_deriv_imp_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean)
-/
@[path]
lemma zero_deriv_imp_constant
  {f : ℝ → ℝ}
  {I : Set ℝ}
-- given
  (hI : Convex ℝ I)
  (hfd : DifferentiableOn ℝ f I)
  (hf' : ∀ x ∈ I, deriv f x = 0) :
-- imply
  ∀ x ∈ I, ∀ y ∈ I, f x = f y := by
-- proof
  intro x hx y hy
  have hfc : ContinuousOn f I := hfd.continuousOn
  have hDiffInt : DifferentiableOn ℝ f (interior I) := hfd.mono interior_subset
  have hDerivNN : ∀ z ∈ interior I, (0 : ℝ) ≤ deriv f z := by
    intro z hz; rw [hf' z (interior_subset hz)]
  have hDerivNP : ∀ z ∈ interior I, deriv f z ≤ (0 : ℝ) := by
    intro z hz; rw [hf' z (interior_subset hz)]
  have hmono : MonotoneOn f I :=
    monotoneOn_of_deriv_nonneg hI hfc hDiffInt hDerivNN
  have hanti : AntitoneOn f I :=
    antitoneOn_of_deriv_nonpos hI hfc hDiffInt hDerivNP
  obtain hle | hle := le_total x y
  · exact le_antisymm (hmono hx hy hle) (hanti hx hy hle)
  · exact (le_antisymm (hmono hy hx hle) (hanti hy hx hle)).symm

/--
[monotonicity_and_derivatives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean)
-/
@[path]
lemma monotonicity_and_derivatives
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (_hab : a < b)
  (hfc : ContinuousOn f (Set.Icc a b))
  (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
-- imply
  (MonotoneOn f (Set.Icc a b) ↔ ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x) ∧ (AntitoneOn f (Set.Icc a b) ↔ ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) := by
-- proof
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hint : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  have hDiffOn : DifferentiableOn ℝ f (interior (Set.Icc a b)) := by
    rw [hint]
    intro x hx
    exact (hfd x hx).differentiableWithinAt
  constructor
  ·
    constructor
    ·
      intro hmono x hx
      have hxab : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
      have hdiff : DifferentiableAt ℝ f x := hfd x hx
      have htend := hdiff.hasDerivAt.tendsto_slope_zero_right
      apply ge_of_tendsto htend
      have hxb : x < b := hx.2
      have hev_lt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < b - x :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      have hev_pos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t :=
        eventually_nhdsWithin_of_forall (fun _ hx => hx)
      apply (hev_pos.and hev_lt).mono
      intro t ⟨ht_pos, ht_lt⟩
      have hxt : x + t ∈ Set.Icc a b := ⟨by linarith [hx.1], by linarith⟩
      have hle : f x ≤ f (x + t) := hmono hxab hxt (by linarith)
      simp only [smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht_pos)) (sub_nonneg.mpr hle)
    ·
      intro hnn
      exact monotoneOn_of_deriv_nonneg hconv hfc hDiffOn (fun x hx => hnn x (hint ▸ hx))
  ·
    constructor
    ·
      intro hanti x hx
      have hxab : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
      have hdiff : DifferentiableAt ℝ f x := hfd x hx
      have htend := hdiff.hasDerivAt.tendsto_slope_zero_right
      apply le_of_tendsto htend
      have hxb : x < b := hx.2
      have hev_lt : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < b - x :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      have hev_pos : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < t :=
        eventually_nhdsWithin_of_forall (fun _ hx => hx)
      apply (hev_pos.and hev_lt).mono
      intro t ⟨ht_pos, ht_lt⟩
      have hxt : x + t ∈ Set.Icc a b := ⟨by linarith [hx.1], by linarith⟩
      have hle : f (x + t) ≤ f x := hanti hxab hxt (by linarith)
      simp only [smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht_pos)) (sub_nonpos.mpr hle)
    ·
      intro hnn
      exact antitoneOn_of_deriv_nonpos hconv hfc hDiffOn (fun x hx => hnn x (hint ▸ hx))


-- created on 2026-10-23
