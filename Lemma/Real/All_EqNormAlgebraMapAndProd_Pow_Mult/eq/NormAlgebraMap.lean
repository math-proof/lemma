import Mathlib
import sympy.Basic

open NumberField

/--
[NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm.lean)
-/
@[main]
private lemma main
  [Field K] [NumberField K]
  {x : K} :
-- imply
  (∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x) ∧
    ∏ v : InfinitePlace K, v x ^ v.mult = ‖algebraMap K (InfiniteAdeleRing K) x‖ := by
-- proof
  have h : ∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x := by
    intro v
    rw [NumberField.InfiniteAdeleRing.algebraMap_apply]
    exact UniformSpace.Completion.norm_coe _
  refine ⟨h, ?_⟩
  rw [NumberField.InfiniteAdeleRing.norm_def]
  exact Finset.prod_congr rfl fun v _ => by rw [h v]


-- created on 2026-10-05
