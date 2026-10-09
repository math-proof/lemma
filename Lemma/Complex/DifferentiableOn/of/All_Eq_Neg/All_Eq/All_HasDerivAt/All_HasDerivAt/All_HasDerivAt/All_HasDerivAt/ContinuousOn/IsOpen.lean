import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.LoomanMenchoff

/--
[looman_menchoff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/LoomanMenchoff.lean)
-/
@[path]
private lemma looman_menchoff_eq
-- given
  {s : Set ℂ} {f : ℂ → ℂ} {ux uy vx vy : ℂ → ℝ}
  (hs : IsOpen s)
  (hf : ContinuousOn f s)
  (hux : ∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ))).re) (ux z) 0)
  (huy : ∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ) * Complex.I)).re) (uy z) 0)
  (hvx : ∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ))).im) (vx z) 0)
  (hvy : ∀ z ∈ s, HasDerivAt (fun t : ℝ => (f (z + (t : ℂ) * Complex.I)).im) (vy z) 0)
  (hcr1 : ∀ z ∈ s, ux z = vy z)
  (hcr2 : ∀ z ∈ s, uy z = -(vx z)) :
-- imply
  DifferentiableOn ℂ f s := by
-- proof
  apply MetaMathlibExt.looman_menchoff hs hf hux huy hvx hvy hcr1 hcr2


-- created on 2026-10-09
