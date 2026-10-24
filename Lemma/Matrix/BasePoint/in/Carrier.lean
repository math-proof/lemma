import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers
open Set AffineHyperplane
open scoped InnerProductSpace


namespace AffineHyperplane

/--
[basePoint_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean)
-/
@[path]
lemma basePoint_mem_carrier
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
-- given
  (h : AffineHyperplane E) :
-- imply
  h.basePoint ∈ h.carrier := by
-- proof
  simp only [basePoint, carrier, Set.mem_setOf_eq, inner_smul_right, real_inner_self_eq_norm_sq]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h.normal_ne_zero))

end AffineHyperplane

/--
[HalfSpaceConvex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean)
-/
@[path]
lemma HalfSpaceConvex
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
-- given
  (h : AffineHyperplane E) :
-- imply
  Convex ℝ h.positiveHalfSpace := by
-- proof
  intro x hx y hy a b ha hb hab
  simp only [AffineHyperplane.positiveHalfSpace, mem_setOf_eq] at *
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  obtain rfl | ha_pos := eq_or_lt_of_le ha
  · simp at hab; subst hab; simp; linarith
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp at hab; subst hab; simp; linarith
    · have h1 : a * h.offset < a * ⟪h.normal, x⟫_ℝ := mul_lt_mul_of_pos_left hx ha_pos
      have h2 : b * h.offset < b * ⟪h.normal, y⟫_ℝ := mul_lt_mul_of_pos_left hy hb_pos
      have h3 : a * h.offset + b * h.offset = h.offset := by
        have := congr_arg (· * h.offset) hab; simp [add_mul] at this; linarith
      linarith

/--
[HalfSpaceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean)
-/
@[path]
lemma HalfSpaceOpen
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
-- given
  (h : AffineHyperplane E) :
-- imply
  IsOpen h.positiveHalfSpace := by
-- proof
  apply isOpen_lt continuous_const
  exact continuous_const.inner continuous_id


-- created on 2026-10-23
