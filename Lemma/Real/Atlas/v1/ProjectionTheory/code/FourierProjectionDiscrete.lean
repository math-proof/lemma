import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.FourierProjectionDiscrete
open ZMod Finset Complex ProjectionTheory
open scoped ZMod


namespace ProjectionTheory

/--
[dft_discreteProjection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierProjectionDiscrete.lean)
-/
@[path]
lemma dft_discreteProjection
  {p : ℕ}
  [NeZero p]
  {N : ℕ}
  {f : Fin N → ℂ}
  {α : ZMod p} :
-- imply
  ZMod.dft (discreteProjection p f) α = ∑ n : Fin N, (stdAddChar (-((n.val : ZMod p) * α)) : ℂ) * f n := by
-- proof
  simp only [ZMod.dft_apply, discreteProjection, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  have key : ∀ a : ZMod p,
    ∑ n ∈ Finset.univ.filter (fun n : Fin N => (n.val : ZMod p) = a),
      (stdAddChar (-(a * α)) : ℂ) * f n =
    ∑ n ∈ Finset.univ.filter (fun n : Fin N => (n.val : ZMod p) = a),
      (stdAddChar (-((n.val : ZMod p) * α)) : ℂ) * f n := by
    intro a
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    rw [hn]
  simp_rw [key]
  rw [← Finset.sum_fiberwise Finset.univ (fun n : Fin N => (n.val : ZMod p))
    (fun n => (stdAddChar (-((n.val : ZMod p) * α)) : ℂ) * f n)]

end ProjectionTheory


-- created on 2026-10-23
