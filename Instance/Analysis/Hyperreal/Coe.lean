import Mathlib.Analysis.Real.Hyperreal


/-- Pointwise lift ℝ → ℝ to ℝ* → ℝ* via Filter.Germ.map.

Lets MersenneFreq write `id (ℝ* → ℝ*) f` / `id (ℝ* → ℝ*) (deriv (u t))`
(lean.js can render the `id` ascription as `f`) instead of `Filter.Germ.map f`.
Greedy: any expected type ℝ* → ℝ* may insert this Coe; bare
`(deriv … : ℝ* → ℝ*)` still fails (expected type infects `deriv`). -/
noncomputable instance : Coe (ℝ → ℝ) (ℝ* → ℝ*) where
  coe := Filter.Germ.map
