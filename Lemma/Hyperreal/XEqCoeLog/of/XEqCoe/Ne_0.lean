import Lemma.Hyperreal.InfinitesimalLogSub.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.XEq.NotInfinite
import Lemma.Hyperreal.XEq.of.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import sympy.Basic
open Hyperreal


/--
`log` is continuous at a nonzero real `r`: if `x ≈ r` (hyperreal closeness to a real) then `log x ≈ log r`.
-/
@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h_r : r ≠ 0)
  (h : x ≈ (r : ℝ*)) :
-- imply
  Log.log x ≈ ((Real.log r : ℝ) : ℝ*) := by
-- proof
  have h_ni : ¬ (((r : ℝ) : ℝ*) → ∞) := by
    have := Hyperreal.archimedeanClassMk_coe_nonneg r
    exact not_lt.mpr this
  have hsub := InfinitesimalSub.of.XEq.NotInfinite h_ni h.symm
  have hsub' : (x - (r : ℝ*)) → 0 := by
    have h1 := (Infinitesimal.is.InfinitesimalNeg ((r : ℝ*) - x)).mp hsub
    rwa [neg_sub] at h1
  exact XEq.of.InfinitesimalSub (InfinitesimalLogSub.of.InfinitesimalSub h_r hsub')


-- created on 2026-10-01
