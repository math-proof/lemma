import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Hyperreal.InfinitesimalSub.of.XEq.NotInfinite
import sympy.Basic
open Hyperreal


/--
Strict order is detected by the real parts: if \( x \approx r \) and \( y \approx s \) for reals \( r < s \), then \( x < y \).
-/
@[main]
private lemma main
  {x y : ℝ*}
  {r s : ℝ}
-- given
  (hx : x ≈ (r : ℝ*))
  (hy : y ≈ (s : ℝ*))
  (h : r < s) :
-- imply
  x < y := by
-- proof
  have h_ni : ∀ t : ℝ, ¬ (((t : ℝ) : ℝ*) → ∞) := fun t => not_lt.mpr (Hyperreal.archimedeanClassMk_coe_nonneg t)
  have hx' := InfinitesimalSub.of.XEq.NotInfinite (h_ni r) hx.symm
  have hy' := InfinitesimalSub.of.XEq.NotInfinite (h_ni s) hy.symm
  have hδ : (0 : ℝ) < (s - r) / 2 := by linarith
  have h1 := (Infinitesimal.is.All_LtAbs _).mp hx' ⟨(s - r) / 2, hδ⟩
  have h2 := (Infinitesimal.is.All_LtAbs _).mp hy' ⟨(s - r) / 2, hδ⟩
  have h1x := (abs_lt.mp h1).1
  have h2y := (abs_lt.mp h2).2
  push_cast at h1x h2y
  linarith


-- created on 2026-10-01