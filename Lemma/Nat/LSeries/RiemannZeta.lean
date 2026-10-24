import Mathlib
import sympy.Basic


/--
[meromorphicOn_riemannZeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannZeta.lean)
-/
@[path]
lemma meromorphicOn_riemannZeta
  :
-- imply
  MeromorphicOn riemannZeta Set.univ := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-23
