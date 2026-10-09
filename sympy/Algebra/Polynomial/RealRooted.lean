import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Real-rooted complex polynomials

A complex polynomial is *real-rooted* if every member of its root multiset
is real.  This file defines the predicate `Polynomial.IsRealRooted`, the
auxiliary quantity `Polynomial.maxRealRoot` (the largest real part of a
root, defaulting to zero), and proves that a monic real-rooted polynomial
is positive to the right of its largest root and nonnegative on the
closed half-line to the right of it.
-/

open scoped ComplexOrder

namespace Polynomial

/-- A complex polynomial is real-rooted if every member of its root multiset is real. -/
def IsRealRooted (p : Polynomial ℂ) : Prop :=
  ∀ z ∈ p.roots, z.im = 0

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

/-- The largest real part of a root, with value zero for a polynomial without roots. -/
noncomputable def maxRealRoot (p : Polynomial ℂ) : ℝ :=
  if h : (p.roots.map Complex.re).toFinset.Nonempty then
    (p.roots.map Complex.re).toFinset.max' h
  else 0

/-- The real part of every root is at most `maxRealRoot`. -/
theorem root_re_le_maxRealRoot {p : Polynomial ℂ} {z : ℂ} (hz : z ∈ p.roots) :
    z.re ≤ p.maxRealRoot := by
  classical
  rw [maxRealRoot]
  split_ifs with h
  · apply Finset.le_max'
    simpa using Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  · exfalso
    apply h
    exact ⟨z.re, by simpa using Multiset.mem_map.mpr ⟨z, hz, rfl⟩⟩

/-- A polynomial with a root has a root whose real part is `maxRealRoot`. -/
theorem exists_root_re_eq_maxRealRoot {p : Polynomial ℂ} (hp : p.roots ≠ 0) :
    ∃ z ∈ p.roots, z.re = p.maxRealRoot := by
  classical
  have hnonempty : (p.roots.map Complex.re).toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    simpa only [ne_eq, Multiset.map_eq_zero] using hp
  rw [maxRealRoot]
  split_ifs with h
  · have hmem := Finset.max'_mem (p.roots.map Complex.re).toFinset h
    rw [Multiset.mem_toFinset] at hmem
    obtain ⟨z, hz, hzeq⟩ := Multiset.mem_map.mp hmem
    exact ⟨z, hz, hzeq⟩
  · exact (h hnonempty).elim

/-- A positive-degree complex polynomial has at least one root. -/
theorem roots_ne_zero_of_natDegree_pos {p : Polynomial ℂ} (hp : 0 < p.natDegree) :
    p.roots ≠ 0 := by
  intro hzero
  have hdegree : p.natDegree = 0 :=
    (IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero (k := ℂ) (p := p)).mp hzero
  omega

/-- For a real-rooted polynomial of positive degree, `maxRealRoot` is itself a root. -/
theorem coe_maxRealRoot_mem_roots {p : Polynomial ℂ} (hp : p.IsRealRooted)
    (hdegree : 0 < p.natDegree) : (p.maxRealRoot : ℂ) ∈ p.roots := by
  obtain ⟨z, hz, hreal⟩ :=
    exists_root_re_eq_maxRealRoot (roots_ne_zero_of_natDegree_pos hdegree)
  have him : z.im = 0 := hp z hz
  have hzeq : z = (p.maxRealRoot : ℂ) := by
    apply Complex.ext
    · simpa using hreal
    · simpa using him
  rwa [← hzeq]

/-- A monic real-rooted polynomial is positive to the right of its largest root. -/
theorem eval_re_pos_of_maxRealRoot_lt {p : Polynomial ℂ} (hmonic : p.Monic)
    (hrooted : p.IsRealRooted) {x : ℝ} (hx : p.maxRealRoot < x) :
    0 < (p.eval (x : ℂ)).re := by
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  have hprod : 0 < (p.roots.map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_pos
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.pos_iff]
    constructor
    · exact sub_pos.mpr (lt_of_le_of_lt (root_re_le_maxRealRoot hz) hx)
    · simpa using hrooted z hz
  exact (RCLike.pos_iff.mp hprod).1

/-- A monic real-rooted polynomial is nonnegative at and to the right of its largest root. -/
theorem eval_re_nonneg_of_maxRealRoot_le {p : Polynomial ℂ} (hmonic : p.Monic)
    (hrooted : p.IsRealRooted) {x : ℝ} (hx : p.maxRealRoot ≤ x) :
    0 ≤ (p.eval (x : ℂ)).re := by
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  have hprod : 0 ≤ (p.roots.map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_nonneg
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.nonneg_iff]
    constructor
    · exact sub_nonneg.mpr (root_re_le_maxRealRoot hz |>.trans hx)
    · simpa using hrooted z hz
  exact (RCLike.nonneg_iff.mp hprod).1

end Polynomial
