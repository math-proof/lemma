import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodic2D
open MeasureTheory StatMech StatMech.Onsager


/--
[continuous_intervalIntegral_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodic2D.lean)
-/
@[path]
private lemma continuous_intervalIntegral_right_eq
  {f : ℝ → ℝ → ℝ}
  {a b : ℝ}
-- given
  (hf : Continuous (Function.uncurry f)) :
-- imply
  Continuous (fun x => ∫ y in a..b, f x y) := by
-- proof
  apply StatMech.Onsager.continuous_intervalIntegral_right f hf a b

/--
[ons_riemann_periodic_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodic2D.lean)
-/
@[path]
private lemma ons_riemann_periodic_two_eq
  {f : ℝ → ℝ → ℝ}
-- given
  (hf : Continuous (Function.uncurry f))
  (hper : ∀ y, Function.Periodic (fun x => f x y) (2 * Real.pi)) :
-- imply
  Filter.Tendsto (fun n : ℕ => (2 * Real.pi / n) ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (2 * Real.pi * i / n) (2 * Real.pi * j / n)) Filter.atTop (nhds (∫ x in (0)..(2 * Real.pi), ∫ y in (0)..(2 * Real.pi), f x y)) := by
-- proof
  apply StatMech.Onsager.ons_riemann_periodic_two f hf hper

/--
[ons_riemann_periodic_two_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodic2D.lean)
-/
@[path]
private lemma ons_riemann_periodic_two_shift_eq
  {f : ℝ → ℝ → ℝ}
  {s t : ℝ}
-- given
  (hf : Continuous (Function.uncurry f))
  (hper : ∀ y, Function.Periodic (fun x => f x y) (2 * Real.pi))
  (hs : s ∈ Set.Icc (0 : ℝ) 1)
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  Filter.Tendsto (fun n : ℕ => (2 * Real.pi / n) ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f (2 * Real.pi * (i + s) / n) (2 * Real.pi * (j + t) / n)) Filter.atTop (nhds (∫ x in (0)..(2 * Real.pi), ∫ y in (0)..(2 * Real.pi), f x y)) := by
-- proof
  apply StatMech.Onsager.ons_riemann_periodic_two_shift f hf hper s t hs ht


-- created on 2026-10-23
