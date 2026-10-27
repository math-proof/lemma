import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
open Filter Set Topology StatMech StatMech.FrontierA


/--
[isingBoxPressure_tendsto_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma isingBoxPressure_tendsto_limit_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ) :
-- imply
  Tendsto (isingBoxPressureSeq d beta h) atTop (nhds (isingBoxPressureLimit d hd beta h)) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressure_tendsto_limit d hd beta h

/--
[isingBoxPressureSeq_convexOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma isingBoxPressureSeq_convexOn_field_eq
  {d n : ℕ}
  {beta : ℝ} :
-- imply
  ConvexOn ℝ univ (fun h => isingBoxPressureSeq d beta h n) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureSeq_convexOn_field d n beta

/--
[isingBoxPressureSeq_hasDerivAt_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma isingBoxPressureSeq_hasDerivAt_field_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun x => isingBoxPressureSeq d beta x n) (isingBoxPressureFieldDerivative d n beta h) h := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureSeq_hasDerivAt_field d n beta h

/--
[leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  leeYangNormalizedFieldLogDerivative (boxGraph d n) beta (h : ℂ) = (isingBoxPressureFieldDerivative d n beta h : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative d n beta h

/--
[isingBoxPressureLimit_convexOn_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma isingBoxPressureLimit_convexOn_field_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ConvexOn ℝ univ (isingBoxPressureLimit d hd beta) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureLimit_convexOn_field d hd beta

/--
[leeYangPressureRegularRealSet_countable_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangPressureRegularRealSet_countable_compl_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (leeYangPressureRegularRealSet d hd beta)ᶜ.Countable := by
-- proof
  apply StatMech.FrontierA.leeYangPressureRegularRealSet_countable_compl d hd beta

/--
[isingBoxPressureFieldDerivative_tendsto_of_regular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma isingBoxPressureFieldDerivative_tendsto_of_regular_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ)
  (hh : h ∈ leeYangPressureRegularRealSet d hd beta) :
-- imply
  Tendsto (fun n => isingBoxPressureFieldDerivative d n beta h) atTop (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
-- proof
  apply StatMech.FrontierA.isingBoxPressureFieldDerivative_tendsto_of_regular d hd beta h hh

/--
[leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h : ℝ)
  (hh : h ∈ leeYangPressureRegularRealSet d hd beta) :
-- imply
  Tendsto (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta (h : ℂ)) atTop (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h : ℂ)) := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular d hd beta h hh

/--
[leeYangRightRealAnchor_subset_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangRightRealAnchor_subset_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  leeYangRightRealAnchor d hd beta ⊆ {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangRightRealAnchor_subset_rightHalfPlane d hd beta

/--
[leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor_eq
  {d : ℕ}
  {beta : ℝ}
  {z : ℂ}
-- given
  (hd : 1 ≤ d)
  (hz : z ∈ leeYangRightRealAnchor d hd beta) :
-- imply
  Tendsto (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta z) atTop (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) z.re : ℂ)) := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor d hd beta hz

/--
[leeYangRightRealAnchor_frequently_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangRightRealAnchor_frequently_near_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h₀ : ℝ)
  (hh₀ : 0 < h₀) :
-- imply
  ∃ᶠ z in nhdsWithin (h₀ : ℂ) ({(h₀ : ℂ)}ᶜ), z ∈ leeYangRightRealAnchor d hd beta := by
-- proof
  apply StatMech.FrontierA.leeYangRightRealAnchor_frequently_near d hd beta h₀ hh₀

/--
[leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hcompact : IsLocallyUniformlySequentiallyPrecompact (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {z : ℂ | 0 < z.re}) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧ TendstoLocallyUniformlyOn (deriv ∘ fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) (deriv g) atTop {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact d hd hbeta hcompact

/--
[leeYangLeftRealAnchor_subset_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangLeftRealAnchor_subset_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  leeYangLeftRealAnchor d hd beta ⊆ {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangLeftRealAnchor_subset_leftHalfPlane d hd beta

/--
[leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor_eq
  {d : ℕ}
  {beta : ℝ}
  {z : ℂ}
-- given
  (hd : 1 ≤ d)
  (hz : z ∈ leeYangLeftRealAnchor d hd beta) :
-- imply
  Tendsto (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta z) atTop (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) z.re : ℂ)) := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor d hd beta hz

/--
[leeYangLeftRealAnchor_frequently_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangLeftRealAnchor_frequently_near_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (beta h₀ : ℝ)
  (hh₀ : h₀ < 0) :
-- imply
  ∃ᶠ z in nhdsWithin (h₀ : ℂ) ({(h₀ : ℂ)}ᶜ), z ∈ leeYangLeftRealAnchor d hd beta := by
-- proof
  apply StatMech.FrontierA.leeYangLeftRealAnchor_frequently_near d hd beta h₀ hh₀

/--
[leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hcompact : IsLocallyUniformlySequentiallyPrecompact (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {z : ℂ | z.re < 0}) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧ TendstoLocallyUniformlyOn (deriv ∘ fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) (deriv g) atTop {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact d hd hbeta hcompact


-- created on 2026-10-23
