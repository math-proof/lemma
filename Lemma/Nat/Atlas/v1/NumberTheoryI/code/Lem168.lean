import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.Lem168
open MeasureTheory Set Filter Topology Asymptotics Real IntegralCriterion


/--
[lem_16_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
lemma lem_16_8
  {f : ℝ → ℝ}
-- given
  (hf_mono : Monotone f)
  (hf_conv : ∃ L : ℝ, Filter.Tendsto (fun x => ∫ t in Set.Ioc 1 x, (f t - t) / t ^ 2) Filter.atTop (𝓝 L)) :
-- imply
  (fun x : ℝ => f x) ~[Filter.atTop] (fun x => x) :=
-- proof
  IntegralCriterion.lem_16_8_integral_criterion f hf_mono hf_conv
namespace Lem168

/--
[cauchy_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma cauchy_of_tendsto_eq
  {F : ℝ → ℝ}
  {L : ℝ}
-- given
  (hF : Tendsto F atTop (𝓝 L)) :
-- imply
  ∀ c > 0, ∀ᶠ x in atTop, ∀ y, x ≤ y → |F y - F x| < c := by
-- proof
  apply IntegralCriterion.cauchy_of_tendsto hF

/--
[integrableOn_g_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma integrableOn_g_Ioc_eq
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hf : Monotone f)
  (ha : 0 < a) :
-- imply
  IntegrableOn (fun t => (f t - t) / t ^ 2) (Ioc a b) := by
-- proof
  apply IntegralCriterion.integrableOn_g_Ioc f hf a b ha

/--
[integral_Ioc_split'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma integral_Ioc_split'_eq
  {g : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hab : a ≤ b)
  (hbc : b ≤ c)
  (hg1 : IntegrableOn g (Ioc a b))
  (hg2 : IntegrableOn g (Ioc b c)) :
-- imply
  ∫ x in Ioc a c, g x = (∫ x in Ioc a b, g x) + (∫ x in Ioc b c, g x) := by
-- proof
  apply IntegralCriterion.integral_Ioc_split' hab hbc hg1 hg2

/--
[integral_const_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma integral_const_Ioc_eq
  {a b : ℝ}
  {c : ℝ}
-- given
  (hab : a ≤ b) :
-- imply
  ∫ _ in Ioc a b, c = c * (b - a) := by
-- proof
  apply IntegralCriterion.integral_const_Ioc hab c

/--
[upper_bound_of_convergent_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma upper_bound_of_convergent_integral_eq
  {f : ℝ → ℝ}
  {L : ℝ}
  {lam : ℝ}
-- given
  (hf_mono : Monotone f)
  (hL : Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L))
  (hlam : 1 < lam) :
-- imply
  ∀ᶠ x in atTop, f x < lam * x := by
-- proof
  apply IntegralCriterion.upper_bound_of_convergent_integral f hf_mono hL hlam

/--
[lower_bound_of_convergent_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma lower_bound_of_convergent_integral_eq
  {f : ℝ → ℝ}
  {L : ℝ}
  {lam : ℝ}
-- given
  (hf_mono : Monotone f)
  (hL : Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L))
  (hlam : 1 < lam) :
-- imply
  ∀ᶠ x in atTop, x / lam < f x := by
-- proof
  apply IntegralCriterion.lower_bound_of_convergent_integral f hf_mono hL hlam

/--
[lem_16_8_integral_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem168.lean)
-/
@[path]
private lemma lem_16_8_integral_criterion_eq
  {f : ℝ → ℝ}
-- given
  (hf_mono : Monotone f)
  (hf_conv : ∃ L : ℝ, Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L)) :
-- imply
  (fun x : ℝ => f x) ~[atTop] (fun x => x) := by
-- proof
  apply IntegralCriterion.lem_16_8_integral_criterion f hf_mono hf_conv


-- created on 2026-10-23
