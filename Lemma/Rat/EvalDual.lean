import Mathlib
import sympy.Basic
import Lemma.DualSelmer.ExtConditions
import Lemma.GroupCohomology.CupProduct
import Lemma.Int.P2MUtil
open CategoryTheory
open Int


namespace Definitions
end Definitions

/--
[Rep_isEquivariantBilinear_eval_dualTwist](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_isEquivariantBilinear_eval_dualTwist.lean)
-/
@[path]
private lemma main
  {k G : Type u} [Field k] [Group G]
  {M : Rep.{u} k G}
  {χ : G →* kˣ} :
-- imply
  Rep.IsEquivariantBilinear M (M.dualTwist χ) (groupCohomology.ofChar χ)
    (Module.Dual.eval k M : M →ₗ[k] M.dualTwist χ →ₗ[k] groupCohomology.ofChar χ) := by
-- proof
  intro g m f
  show ((M.dualTwist χ).ρ g f) (M.ρ g m) = (groupCohomology.ofChar χ).ρ g (f m)
  rw [Rep.dualTwist_ρ_apply, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]
  show (χ g : k) • f m = ((Representation.trivial k G k).twist χ) g (f m)
  rw [Representation.twist_apply_apply]
  simp


-- created on 2026-10-24
