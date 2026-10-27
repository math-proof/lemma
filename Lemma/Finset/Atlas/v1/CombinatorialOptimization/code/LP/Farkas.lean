import Mathlib
import Initialize.Tactic.Attr.Basic
open Matrix


/--
[clm_repr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/LP/Farkas.lean)
-/
@[path]
lemma clm_repr
  {m : ℕ}
  {f : (Fin m → ℝ) →L[ℝ] ℝ}
  {v : Fin m → ℝ} :
-- imply
  f v = dotProduct (fun i => f (Pi.single i 1 : Fin m → ℝ)) v := by
-- proof
  simp only [dotProduct]
  have hv : v = ∑ i : Fin m, (v i) • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Finset.mem_univ]
  conv_lhs => rw [hv]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]


-- created on 2026-10-23
