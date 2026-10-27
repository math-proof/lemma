import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.LoewnerProps.Part4
open Complex Set Filter Topology StatMech StatMech.SLE


/--
[im_loewnerField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma im_loewnerField_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {w : ℂ} :
-- imply
  (loewnerField W t w).im = -2 * w.im / Complex.normSq (w - (W t : ℂ)) := by
-- proof
  apply StatMech.SLE.im_loewnerField W t w

/--
[im_loewnerField_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma im_loewnerField_nonpos_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {w : ℂ}
-- given
  (hw : 0 ≤ w.im) :
-- imply
  (loewnerField W t w).im ≤ 0 := by
-- proof
  apply StatMech.SLE.im_loewnerField_nonpos hw

/--
[re_loewnerField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma re_loewnerField_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {w : ℂ} :
-- imply
  (loewnerField W t w).re = 2 * (w.re - W t) / Complex.normSq (w - (W t : ℂ)) := by
-- proof
  apply StatMech.SLE.re_loewnerField W t w

/--
[loewnerReflection_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma loewnerReflection_re_eq
  {z : ℂ} :
-- imply
  (loewnerReflection z).re = -z.re := by
-- proof
  apply StatMech.SLE.loewnerReflection_re z

/--
[loewnerReflection_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma loewnerReflection_im_eq
  {z : ℂ} :
-- imply
  (loewnerReflection z).im = z.im := by
-- proof
  apply StatMech.SLE.loewnerReflection_im z

/--
[loewnerReflection_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma loewnerReflection_involutive_eq
  {z : ℂ} :
-- imply
  loewnerReflection (loewnerReflection z) = z := by
-- proof
  apply StatMech.SLE.loewnerReflection_involutive z

/--
[loewnerReflection_loewnerField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma loewnerReflection_loewnerField_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {w : ℂ} :
-- imply
  loewnerReflection (loewnerField W t w) = loewnerField (fun s ↦ -W s) t (loewnerReflection w) := by
-- proof
  apply StatMech.SLE.loewnerReflection_loewnerField W t w

/--
[hasDerivAt_im_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasDerivAt_im_of_eq
  {g : ℝ → ℂ}
  {v : ℂ}
  {t : ℝ}
-- given
  (h : HasDerivAt g v t) :
-- imply
  HasDerivAt (fun u => (g u).im) v.im t := by
-- proof
  apply StatMech.SLE.hasDerivAt_im_of h

/--
[hasDerivWithinAt_im_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasDerivWithinAt_im_of_eq
  {g : ℝ → ℂ}
  {v : ℂ}
  {s : Set ℝ}
  {t : ℝ}
-- given
  (h : HasDerivWithinAt g v s t) :
-- imply
  HasDerivWithinAt (fun u => (g u).im) v.im s t := by
-- proof
  apply StatMech.SLE.hasDerivWithinAt_im_of h

/--
[hasDerivAt_re_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasDerivAt_re_of_eq
  {g : ℝ → ℂ}
  {v : ℂ}
  {t : ℝ}
-- given
  (h : HasDerivAt g v t) :
-- imply
  HasDerivAt (fun u => (g u).re) v.re t := by
-- proof
  apply StatMech.SLE.hasDerivAt_re_of h

/--
[hasDerivWithinAt_re_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasDerivWithinAt_re_of_eq
  {g : ℝ → ℂ}
  {v : ℂ}
  {s : Set ℝ}
  {t : ℝ}
-- given
  (h : HasDerivWithinAt g v s t) :
-- imply
  HasDerivWithinAt (fun u => (g u).re) v.re s t := by
-- proof
  apply StatMech.SLE.hasDerivWithinAt_re_of h

/--
[antitoneOn_im_of_isLoewnerSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma antitoneOn_im_of_isLoewnerSolution_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {a b : ℝ}
  {g : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
  (hd : ∀ t ∈ Ioo a b, HasDerivAt g (loewnerField W t (g t)) t)
  (hs : ∀ t ∈ Ioo a b, g t ∈ loewnerStrip δ) :
-- imply
  AntitoneOn (fun s => (g s).im) (Icc a b) := by
-- proof
  apply StatMech.SLE.antitoneOn_im_of_isLoewnerSolution hδ hcont hd hs

/--
[normSq_sub_ofReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma normSq_sub_ofReal_ge_eq
  {δ : ℝ}
  {x : ℝ}
  {w : ℂ}
-- given
  (hw : δ ≤ w.im)
  (hδ : 0 ≤ δ) :
-- imply
  δ ^ 2 ≤ Complex.normSq (w - (x : ℂ)) := by
-- proof
  apply StatMech.SLE.normSq_sub_ofReal_ge hw hδ

/--
[im_ge_exp_mul_of_isLoewnerSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma im_ge_exp_mul_of_isLoewnerSolution_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {a b : ℝ}
  {g : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
  (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
  (hs : ∀ t ∈ Ico a b, g t ∈ loewnerStrip δ) :
-- imply
  ∀ t ∈ Icc a b, (g a).im * Real.exp (-(2 / δ ^ 2) * (t - a)) ≤ (g t).im := by
-- proof
  apply StatMech.SLE.im_ge_exp_mul_of_isLoewnerSolution hδ hcont hd hs

/--
[im_ge_exp_mul_of_normSq_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma im_ge_exp_mul_of_normSq_ge_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {a b : ℝ}
  {g : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
  (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
  (hupper : ∀ t ∈ Ico a b, 0 ≤ (g t).im)
  (hden : ∀ t ∈ Ico a b, δ ^ 2 ≤ Complex.normSq (g t - (W t : ℂ))) :
-- imply
  ∀ t ∈ Icc a b, (g a).im * Real.exp (-(2 / δ ^ 2) * (t - a)) ≤ (g t).im := by
-- proof
  apply StatMech.SLE.im_ge_exp_mul_of_normSq_ge hδ hcont hd hupper hden

/--
[mem_upperHalfPlane_of_isLoewnerSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma mem_upperHalfPlane_of_isLoewnerSolution_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {a b : ℝ}
  {g : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
  (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
  (hs : ∀ t ∈ Ico a b, g t ∈ loewnerStrip δ)
  (h0 : 0 < (g a).im) :
-- imply
  ∀ t ∈ Icc a b, g t ∈ upperHalfPlane := by
-- proof
  apply StatMech.SLE.mem_upperHalfPlane_of_isLoewnerSolution hδ hcont hd hs h0

/--
[eventually_ne_zero_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma eventually_ne_zero_cocompact_eq :
-- imply
  ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
-- proof
  apply StatMech.SLE.eventually_ne_zero_cocompact

/--
[tendsto_inv_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma tendsto_inv_cocompact_eq :
-- imply
  Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
-- proof
  apply StatMech.SLE.tendsto_inv_cocompact

/--
[tendsto_cocompact_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma tendsto_cocompact_of_sub_eq
  {f : ℂ → ℂ}
-- given
  (hf : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0)) :
-- imply
  Tendsto f (cocompact ℂ) (cocompact ℂ) := by
-- proof
  apply StatMech.SLE.tendsto_cocompact_of_sub hf

/--
[eventually_ne_zero_of_tendsto_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma eventually_ne_zero_of_tendsto_cocompact_eq
  {f : ℂ → ℂ}
-- given
  (hfc : Tendsto f (cocompact ℂ) (cocompact ℂ)) :
-- imply
  ∀ᶠ z in cocompact ℂ, f z ≠ 0 := by
-- proof
  apply StatMech.SLE.eventually_ne_zero_of_tendsto_cocompact hfc

/--
[tendsto_div_self_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma tendsto_div_self_cocompact_eq
  {f : ℂ → ℂ}
-- given
  (hf : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0)) :
-- imply
  Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1) := by
-- proof
  apply StatMech.SLE.tendsto_div_self_cocompact hf

/--
[tendsto_self_div_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma tendsto_self_div_cocompact_eq
  {f : ℂ → ℂ}
-- given
  (hf : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0)) :
-- imply
  Tendsto (fun z => z / f z) (cocompact ℂ) (𝓝 1) := by
-- proof
  apply StatMech.SLE.tendsto_self_div_cocompact hf

/--
[hasHalfPlaneCapacity_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_comp_eq
  {f g : ℂ → ℂ}
  {a b : ℝ}
-- given
  (hf : HasHalfPlaneCapacity f a)
  (hg : HasHalfPlaneCapacity g b) :
-- imply
  HasHalfPlaneCapacity (g ∘ f) (a + b) := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_comp hf hg

/--
[hasHalfPlaneCapacity_comp_id_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_comp_id_right_eq
  {f : ℂ → ℂ}
  {a : ℝ}
-- given
  (hf : HasHalfPlaneCapacity f a) :
-- imply
  HasHalfPlaneCapacity (f ∘ id) a := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_comp_id_right hf

/--
[hasHalfPlaneCapacity_comp_id_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_comp_id_left_eq
  {f : ℂ → ℂ}
  {a : ℝ}
-- given
  (hf : HasHalfPlaneCapacity f a) :
-- imply
  HasHalfPlaneCapacity (id ∘ f) a := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_comp_id_left hf

/--
[HasCapacityRate.hcap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hcap_zero_eq
  {g : ℝ → ℂ → ℂ}
  {a : ℝ}
-- given
  (h : HasCapacityRate g a) :
-- imply
  HasHalfPlaneCapacity (g 0) 0 := by
-- proof
  apply StatMech.SLE.HasCapacityRate.hcap_zero h

/--
[hcap_linear_of_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma hcap_linear_of_decomposition_eq
  {gs gincr gt : ℂ → ℂ}
  {cs ct : ℝ}
-- given
  (hcompose : gt = gincr ∘ gs)
  (hs : HasHalfPlaneCapacity gs cs)
  (hincr : HasHalfPlaneCapacity gincr (ct - cs)) :
-- imply
  HasHalfPlaneCapacity gt ct := by
-- proof
  apply StatMech.SLE.hcap_linear_of_decomposition hcompose hs hincr

/--
[subset_of_monotoneHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma subset_of_monotoneHull_eq
  {K : ℝ → Set ℂ}
  {s t : ℝ}
-- given
  (h : MonotoneHullFamily K)
  (hst : s ≤ t) :
-- imply
  K s ⊆ K t := by
-- proof
  apply StatMech.SLE.subset_of_monotoneHull h hst

/--
[complement_antitone_of_monotoneHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma complement_antitone_of_monotoneHull_eq
  {K : ℝ → Set ℂ}
-- given
  (h : MonotoneHullFamily K) :
-- imply
  Antitone (fun t => upperHalfPlane \ K t) := by
-- proof
  apply StatMech.SLE.complement_antitone_of_monotoneHull h

/--
[isCompactHull_of_monotoneHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean)
-/
@[path]
private lemma isCompactHull_of_monotoneHull_eq
  {K : ℝ → Set ℂ}
  {t : ℝ}
-- given
  (h : MonotoneHullFamily K) :
-- imply
  IsCompactHull (K t) := by
-- proof
  apply StatMech.SLE.isCompactHull_of_monotoneHull h t


-- created on 2026-10-23
