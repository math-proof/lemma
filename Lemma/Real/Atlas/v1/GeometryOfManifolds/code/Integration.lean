import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.Integration
open DifferentialFormSpace StokesIntegration


namespace StokesIntegration

/--
[inner_product_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Integration.lean)
-/
@[path]
lemma inner_product_linear
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {r : ℝ}
  {α₁ α₂ β : Ω p}
-- given
  (S : StokesIntegration (inst := inst)) :
-- imply
  S.inner_prod p (r • α₁ + α₂) β = r * S.inner_prod p α₁ β + S.inner_prod p α₂ β := by
-- proof
  unfold inner_prod
  rw [S.wedge_star_linear_left]
  simp [← S.linear_integrate_eq, map_add, map_smul]

end StokesIntegration

namespace StokesIntegration

/--
[stokes_adjoint_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Integration.lean)
-/
@[path]
lemma stokes_adjoint_identity
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α : Ω p}
  {β : Ω (p + 1)}
-- given
  (S : StokesIntegration (inst := inst)) :
-- imply
  S.inner_prod (p + 1) (inst.d α) β = (-1 : ℝ)^(p + 1) • S.integrate (S.wedge_star_d p α β) := by
-- proof
  unfold inner_prod
  exact S.leibniz_rule p α β

end StokesIntegration


-- created on 2026-10-23
