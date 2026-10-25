import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.osd_slopege
open Real Set StatMech StatMech.Walls


/--
[osd_slope_ge_diffOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_slopege.lean)
-/
@[path]
private lemma osd_slope_ge_diffOn_eq
  {a b m : ℝ}
  {T : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hdiff : DifferentiableOn ℝ T (Icc a b))
  (hbound : ∀ x ∈ Icc a b, m ≤ deriv T x) :
-- imply
  m * (b - a) ≤ T b - T a := by
-- proof
  apply StatMech.Walls.osd_slope_ge_diffOn a b m hab T hdiff hbound

/--
[osd_slope_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_slopege.lean)
-/
@[path]
private lemma osd_slope_ge_eq
  {a b m : ℝ}
  {T T' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt T (T' x) x)
  (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
-- imply
  m * (b - a) ≤ T b - T a := by
-- proof
  apply StatMech.Walls.osd_slope_ge a b m hab T T' hd hbound

/--
[osd_slope_ge_of_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_slopege.lean)
-/
@[path]
private lemma osd_slope_ge_of_hasDerivAt_eq
  {a b m : ℝ}
  {T T' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x, HasDerivAt T (T' x) x)
  (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
-- imply
  m * (b - a) ≤ T b - T a := by
-- proof
  apply StatMech.Walls.osd_slope_ge_of_hasDerivAt a b m hab T T' hd hbound


-- created on 2026-10-23
