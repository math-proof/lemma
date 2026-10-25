import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicMidpoint
open MeasureTheory Filter StatMech StatMech.Onsager


/--
[ons_riemann_periodic_midpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodicMidpoint.lean)
-/
@[path]
private lemma ons_riemann_periodic_midpoint_eq
  {f : Real → Real}
-- given
  (hf : Continuous f)
  (hper : Function.Periodic f (2 * Real.pi)) :
-- imply
  Tendsto (fun n : Nat => (2 * Real.pi / n) * ∑ k ∈ Finset.range n, f (2 * Real.pi * (k + (1 : Real) / 2) / n - Real.pi)) atTop (nhds (∫ x in (-Real.pi)..Real.pi, f x)) := by
-- proof
  apply StatMech.Onsager.ons_riemann_periodic_midpoint f hf hper

/--
[ons_riemann_periodic_midpoint_of_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodicMidpoint.lean)
-/
@[path]
private lemma ons_riemann_periodic_midpoint_of_tendstoUniformly_eq
  {F : Nat → Real → Real}
  {f : Real → Real}
-- given
  (hf : Continuous f)
  (hper : Function.Periodic f (2 * Real.pi))
  (hF : TendstoUniformly F f atTop) :
-- imply
  Tendsto (fun n : Nat => (2 * Real.pi / n) * ∑ k ∈ Finset.range n, F n (2 * Real.pi * (k + (1 : Real) / 2) / n - Real.pi)) atTop (nhds (∫ x in (-Real.pi)..Real.pi, f x)) := by
-- proof
  apply StatMech.Onsager.ons_riemann_periodic_midpoint_of_tendstoUniformly F f hf hper hF

/--
[ons_riemann_periodic_midpoint_average_of_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RiemannPeriodicMidpoint.lean)
-/
@[path]
private lemma ons_riemann_periodic_midpoint_average_of_tendstoUniformly_eq
  {F : Nat → Real → Real}
  {f : Real → Real}
-- given
  (hf : Continuous f)
  (hper : Function.Periodic f (2 * Real.pi))
  (hF : TendstoUniformly F f atTop) :
-- imply
  Tendsto (fun n : Nat => (1 / (n : Real)) * ∑ k ∈ Finset.range n, F n (2 * Real.pi * (k + (1 : Real) / 2) / n - Real.pi)) atTop (nhds ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, f x)) := by
-- proof
  apply StatMech.Onsager.ons_riemann_periodic_midpoint_average_of_tendstoUniformly F f hf hper hF


-- created on 2026-10-23
