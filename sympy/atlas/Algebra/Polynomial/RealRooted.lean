/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RealRooted.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Complex.Polynomial.Basic

import Mathlib.Analysis.Complex.Order

open scoped ComplexOrder

namespace Polynomial
/-- A complex polynomial is real-rooted if every member of its root multiset is real. -/
def IsRealRooted (p : Polynomial ℂ) : Prop :=
  ∀ z ∈ p.roots, z.im = 0

/-- The largest real part of a root, with value zero for a polynomial without roots. -/
noncomputable def maxRealRoot (p : Polynomial ℂ) : ℝ :=
  if h : (p.roots.map Complex.re).toFinset.Nonempty then
    (p.roots.map Complex.re).toFinset.max' h
  else 0
end Polynomial
