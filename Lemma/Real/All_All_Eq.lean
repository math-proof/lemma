import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineReflectionProposition
open Set AffineReflectionGroup
open scoped InnerProductSpace


namespace AffineReflectionGroup

/--
[stabilizer_linearPart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineReflectionProposition.lean)
-/
@[path]
private lemma stabilizer_linearPart_injective
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {x : E} :
-- imply
  ∀ w₁ ∈ W.Stabilizer x, ∀ w₂ ∈ W.Stabilizer x, linearPartHom w₁ = linearPartHom w₂ → w₁ = w₂ := by
-- proof
  intro w₁ hw₁ w₂ hw₂ hlin
  have hw₁_fix : w₁ x = x := hw₁.2
  have hw₂_fix : w₂ x = x := hw₂.2
  suffices h_eq : w₁⁻¹ * w₂ = 1 from
    calc
      _ = w₁ * 1 := (mul_one w₁).symm
      _ = w₁ * (w₁⁻¹ * w₂) := by rw [h_eq]
      _ = w₂ := by rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hker : linearPartHom (w₁⁻¹ * w₂) = 1 := by
    rw [map_mul, map_inv, hlin, inv_mul_cancel]
  have hfix : (w₁⁻¹ * w₂) x = x := by
    show w₁.symm (w₂ x) = x
    rw [hw₂_fix]
    exact w₁.injective (by rw [w₁.apply_symm_apply, hw₁_fix])
  ext y
  show (w₁⁻¹ * w₂) y = (1 : AffineIsometryEquiv ℝ E E) y
  set w := w₁⁻¹ * w₂
  simp only [AffineIsometryEquiv.coe_one, id_eq]
  have hvsub := w.map_vsub y x
  simp only [vsub_eq_sub] at hvsub
  have hy : w y = w x + w.linearIsometryEquiv (y - x) := by
    rw [hvsub]; abel
  rw [hy, hfix]
  have hL : w.linearIsometryEquiv (y - x) = y - x := by
    change (linearPartHom w) (y - x) = y - x
    rw [hker]; simp
  rw [hL]; abel

end AffineReflectionGroup


-- created on 2026-10-23
-- updated on 2026-10-24
