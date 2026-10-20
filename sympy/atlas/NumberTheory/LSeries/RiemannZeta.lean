/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannZeta.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Meromorphicity of the Riemann zeta function

`riemannZeta` is meromorphic on `ℂ`: away from its pole at `s = 1` it equals
`(s - 1)⁻¹ + riemannZeta₀ s`, and `riemannZeta₀` is entire.
-/

/-- The Riemann zeta function is meromorphic on `ℂ`. -/
theorem meromorphicOn_riemannZeta : MeromorphicOn riemannZeta Set.univ := by
  have hInv : MeromorphicOn (fun s : ℂ => (s - 1)⁻¹) Set.univ :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.inv
  have h0 : AnalyticOnNhd ℂ riemannZeta₀ Set.univ := fun x _ =>
    differentiable_riemannZeta₀.analyticAt x
  have heq : (fun s : ℂ => (s - 1)⁻¹ + riemannZeta₀ s) =ᶠ[Filter.codiscreteWithin Set.univ]
      riemannZeta := by
    apply Filter.mem_of_superset (compl_singleton_mem_codiscreteWithin (1 : ℂ))
    intro s hs
    exact (riemannZeta_eq_inv_sub_add hs).symm
  exact (hInv.add h0.meromorphicOn).congr_codiscreteWithin heq isOpen_univ
