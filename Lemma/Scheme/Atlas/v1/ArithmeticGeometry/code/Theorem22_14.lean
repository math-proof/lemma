import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
open WeilDifferential in


/--
[weil_differentials_dim_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_14.lean)
-/
@[path]
lemma weil_differentials_dim_eq_one
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  [Nontrivial Ω]
-- given
  (hsd : WeilDifferentialSubspaceData F k Ω) :
-- imply
  Module.finrank F Ω = 1 :=
-- proof
  weil_differentials_finrank_eq_one (F := F) (k := k) hsd

/--
[weil_differentials_one_dim_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_14.lean)
-/
@[path]
lemma weil_differentials_one_dim_basis
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  [Nontrivial Ω]
  {ω₁ ω₂ : Ω}
-- given
  (hsd : WeilDifferentialSubspaceData F k Ω)
  (hω₁ : ω₁ ≠ 0)
  (hω₂ : ω₂ ≠ 0) :
-- imply
  ∃ f : F, f ≠ 0 ∧ ω₂ = f • ω₁ :=
-- proof
  WeilDifferential.omega_one_dim_of_proportional
    (WeilDifferential.weil_differentials_proportional (F := F) (k := k) hsd) ω₁ ω₂ hω₁ hω₂

/--
[weil_differentials_span_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_14.lean)
-/
@[path]
lemma weil_differentials_span_singleton
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  [Nontrivial Ω]
  {ω₀ : Ω}
  {ω : Ω}
-- given
  (hsd : WeilDifferentialSubspaceData F k Ω)
  (hω₀ : ω₀ ≠ 0) :
-- imply
  ∃ f : F, ω = f • ω₀ := by
-- proof
  by_cases hω : ω = 0
  · exact ⟨0, by simp [hω]⟩
  · obtain ⟨f, _, hf⟩ := weil_differentials_one_dim_basis (F := F) (k := k) hsd ω₀ ω hω₀ hω
    exact ⟨f, hf⟩

/--
[weil_differentials_faithful_action](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_14.lean)
-/
@[path]
lemma weil_differentials_faithful_action
  [Field F]
  [Field k]
  [Algebra k F]
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  {ω₀ : Ω}
  {f : F}
-- given
  (hω₀ : ω₀ ≠ 0)
  (hf : f • ω₀ = 0) :
-- imply
  f = 0 := by
-- proof
  by_contra hf_ne
  have : f • ω₀ ≠ 0 := by
    intro h
    have := congr_arg (f⁻¹ • ·) h
    simp [smul_smul, inv_mul_cancel₀ hf_ne] at this
    exact hω₀ this
  exact absurd hf this


-- created on 2026-10-23
