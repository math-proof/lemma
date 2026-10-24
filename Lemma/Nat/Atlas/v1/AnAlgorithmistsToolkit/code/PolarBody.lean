import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.PolarBody
open RealInnerProductSpace ConvexGeometry


namespace ConvexGeometry

/--
[subset_polarBody_polarBody](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PolarBody.lean)
-/
@[path]
lemma subset_polarBody_polarBody
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {K : Set E} :
-- imply
  K ⊆ polarBody (polarBody K) := by
-- proof
  intro x hx y hy
  rw [real_inner_comm]
  exact hy x hx

end ConvexGeometry

namespace ConvexGeometry

/--
[polarBody_polarBody_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PolarBody.lean)
-/
@[path]
lemma polarBody_polarBody_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  {K : Set E}
-- given
  (hK_convex : Convex ℝ K)
  (hK_closed : IsClosed K)
  (hK_zero : (0 : E) ∈ K) :
-- imply
  polarBody (polarBody K) = K := by
-- proof
  apply Set.Subset.antisymm _ (subset_polarBody_polarBody K)
  intro y hy
  by_contra h
  obtain ⟨f, u, hfK, hfy⟩ := geometric_hahn_banach_closed_point hK_convex hK_closed h
  have hu_pos : 0 < u := by
    have := hfK 0 hK_zero
    simp at this
    exact this
  set v := (InnerProductSpace.toDual ℝ E).symm f
  have hfv : ∀ x : E, f x = @inner ℝ E _ v x := by
    intro x
    have heq : f = (InnerProductSpace.toDual ℝ E) v :=
      ((InnerProductSpace.toDual ℝ E).apply_symm_apply f).symm
    rw [heq, InnerProductSpace.toDual_apply_apply]
  have hvu_mem : (u⁻¹ • v) ∈ polarBody K := by
    intro x hx
    rw [inner_smul_left, RCLike.conj_to_real, ← hfv]
    rw [inv_mul_le_iff₀ hu_pos]
    linarith [hfK x hx]
  have hvu_y : @inner ℝ E _ (u⁻¹ • v) y > 1 := by
    rw [inner_smul_left, RCLike.conj_to_real, ← hfv]
    rw [show (u⁻¹ * f y > 1) ↔ (1 < u⁻¹ * f y) from gt_iff_lt]
    rw [one_lt_inv_mul₀ hu_pos]
    linarith
  have hcontra := hy (u⁻¹ • v) hvu_mem
  have := real_inner_comm (u⁻¹ • v) y
  linarith

end ConvexGeometry


-- created on 2026-10-23
