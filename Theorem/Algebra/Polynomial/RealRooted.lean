import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Order
import Def.Algebra.Polynomial.RealRooted
open scoped ComplexOrder

/-!
# Real-rooted complex polynomials

A complex polynomial is *real-rooted* if every member of its root multiset
is real.  This file defines the predicate `Polynomial.IsRealRooted`, the
auxiliary quantity `Polynomial.maxRealRoot` (the largest real part of a
root, defaulting to zero), and proves that a monic real-rooted polynomial
is positive to the right of its largest root and nonnegative on the
closed half-line to the right of it.
-/


namespace Polynomial

/-- A conjugation-invariant polynomial whose roots lie in the closed lower half-plane is
real-rooted. -/
theorem isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
    (p : Polynomial ℂ) (hp0 : p ≠ 0)
    (hreal : Polynomial.map (starRingEnd ℂ) p = p)
    (hupper : ∀ z ∈ p.roots, z.im ≤ 0) : p.IsRealRooted := by
  intro z hz
  have hzroot : p.eval z = 0 := (Polynomial.mem_roots hp0).mp hz
  have hconj_eval : p.eval (star z) = 0 := by
    have hmap := Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) z
    rw [hreal, hzroot] at hmap
    simpa using hmap
  have hconj : star z ∈ p.roots := (Polynomial.mem_roots hp0).mpr hconj_eval
  have hzle := hupper z hz
  have hconjle := hupper (star z) hconj
  have hstarim : (star z).im = -z.im := by rfl
  rw [hstarim] at hconjle
  linarith

end Polynomial
