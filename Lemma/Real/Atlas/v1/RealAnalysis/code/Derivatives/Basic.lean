import Mathlib
import Initialize.Tactic.Attr.Basic
open Filter Topology


/--
[differentiable_at_iff_limit_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/Basic.lean)
-/
@[path]
lemma differentiable_at_iff_limit_exists
  {f : ℝ → ℝ}
  {c : ℝ} :
-- imply
  DifferentiableAt ℝ f c ↔ ∃ L : ℝ, Filter.Tendsto (fun x => (f x - f c) / (x - c)) (nhdsWithin c {c}ᶜ) (nhds L) := by
-- proof
  constructor
  · intro hd
    exact ⟨deriv f c, by rw [show (fun x => (f x - f c) / (x - c)) = slope f c from
      (slope_fun_def_field f c).symm]; exact hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt⟩
  · rintro ⟨L, hL⟩
    have hslope : Filter.Tendsto (slope f c) (nhdsWithin c {c}ᶜ) (nhds L) := by
      rwa [show (fun x => (f x - f c) / (x - c)) = slope f c from
        (slope_fun_def_field f c).symm] at hL
    exact (hasDerivAt_iff_tendsto_slope.mpr hslope).differentiableAt

/--
[chain_rule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Derivatives/Basic.lean)
-/
@[path]
lemma chain_rule
  {f g : ℝ → ℝ}
  {c : ℝ}
-- given
  (hg : DifferentiableAt ℝ g c)
  (hf : DifferentiableAt ℝ f (g c)) :
-- imply
  DifferentiableAt ℝ (f ∘ g) c ∧ deriv (f ∘ g) c = deriv f (g c) * deriv g c :=
-- proof
  ⟨hf.comp c hg, deriv_comp c hf hg⟩


-- created on 2026-10-23
