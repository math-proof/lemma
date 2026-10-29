import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_meanindicatormono
open MeasureTheory StatMech StatMech.Walls


/--
[oc_mean_indicator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_meanindicatormono.lean)
-/
@[path]
private lemma oc_mean_indicator_mono_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {s t : Set α}
-- given
  (h : s ⊆ t) :
-- imply
  ∫⁻ x, s.indicator (fun _ => (1 : ENNReal)) x ∂μ ≤ ∫⁻ x, t.indicator (fun _ => (1 : ENNReal)) x ∂μ := by
-- proof
  apply StatMech.Walls.oc_mean_indicator_mono μ h

/--
[oc_mean_indicator_mono_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_meanindicatormono.lean)
-/
@[path]
private lemma oc_mean_indicator_mono_pred_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {P Q : α → Prop}
-- given
  (h : ∀ x, P x → Q x) :
-- imply
  ∫⁻ x, {x | P x}.indicator (fun _ => (1 : ENNReal)) x ∂μ ≤ ∫⁻ x, {x | Q x}.indicator (fun _ => (1 : ENNReal)) x ∂μ := by
-- proof
  apply StatMech.Walls.oc_mean_indicator_mono_pred μ h

/--
[oc_indicator_mean_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_meanindicatormono.lean)
-/
@[path]
private lemma oc_indicator_mean_eq_measure_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {s : Set α}
-- given
  (hs : MeasurableSet s) :
-- imply
  ∫⁻ x, s.indicator (fun _ => (1 : ENNReal)) x ∂μ = μ s := by
-- proof
  apply StatMech.Walls.oc_indicator_mean_eq_measure μ hs

/--
[oc_measure_mono_of_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_meanindicatormono.lean)
-/
@[path]
private lemma oc_measure_mono_of_imp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {P Q : α → Prop}
-- given
  (h : ∀ x, P x → Q x) :
-- imply
  μ {x | P x} ≤ μ {x | Q x} := by
-- proof
  apply StatMech.Walls.oc_measure_mono_of_imp μ h

/--
[oc_expect_indicator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_meanindicatormono.lean)
-/
@[path]
private lemma oc_expect_indicator_mono_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hν : IsProbWeight ν)
  (P Q : ConfigSpace E → Prop)
  (hPQ : ∀ ω, P ω → Q ω) :
-- imply
  expect ν (fun ω => if P ω then (1 : ℝ) else 0) ≤ expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc_expect_indicator_mono ν hν P Q hPQ

/--
[oc_expect_indicator_mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_meanindicatormono.lean)
-/
@[path]
private lemma oc_expect_indicator_mono_set_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hν : IsProbWeight ν)
  (hAB : A ⊆ B) :
-- imply
  expect ν (A.indicator (fun _ => (1 : ℝ))) ≤ expect ν (B.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Walls.oc_expect_indicator_mono_set ν hν hAB


-- created on 2026-10-23
