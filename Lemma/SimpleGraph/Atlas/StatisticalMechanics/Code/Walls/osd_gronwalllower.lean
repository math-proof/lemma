import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.osd_gronwalllower
open Real Set StatMech StatMech.Walls


/--
[osd_gronwall_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_gronwalllower.lean)
-/
@[path]
private lemma osd_gronwall_lower_eq
  {a b lam : ℝ}
  {f f' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
-- imply
  Real.exp (lam * (b - a)) * f a ≤ f b := by
-- proof
  apply StatMech.Walls.osd_gronwall_lower a b lam hab f f' hd hineq

/--
[osd_gronwall_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_gronwalllower.lean)
-/
@[path]
private lemma osd_gronwall_decay_eq
  {a b lam M : ℝ}
  {f f' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x)
  (hfb : f b ≤ M) :
-- imply
  f a ≤ M * Real.exp (-(lam * (b - a))) := by
-- proof
  apply StatMech.Walls.osd_gronwall_decay a b lam M hab f f' hd hineq hfb

/--
[osd_gronwall_lower_eq_osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_gronwalllower.lean)
-/
@[path]
private lemma osd_gronwall_lower_eq_osss_eq
  {a b lam : ℝ}
  {f f' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
-- imply
  osd_gronwall_lower a b lam hab f f' hd hineq = StatMech.OSSS.SharpnessFK.gronwall_lower a b lam hab f f' hd hineq := by
-- proof
  apply StatMech.Walls.osd_gronwall_lower_eq_osss a b lam hab f f' hd hineq


-- created on 2026-10-23
