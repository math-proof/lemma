import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.EckartYoung

/--
[EckartYoung](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/EckartYoung.lean)
-/
@[path]
private lemma eckart_young_best_rank_approx_operator_norm_eq
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)
  (k : ℕ) :
-- imply
  sInf { r : ℝ | ∃ S : E →ₗ[𝕜] F, Module.finrank 𝕜 S.range ≤ k ∧ r = ‖(T - S).toContinuousLinearMap‖ } =
    T.singularValues k := by
-- proof
  apply InnerProductSpace.EckartYoungWanted.eckartYoung_best_rank_approx_operator_norm T k

-- created on 2026-10-10
