import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Lemma.Int.OrthogonalSum.eq.Add
open FiniteDimensional Module Garrett


/--
[nondeg_fst_of_orthogonalSum_nondeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/LagrangianDimBound.lean)
-/
@[path]
private lemma nondeg_fst_of_orthogonalSum_nondeg
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂}
-- given
  (h : BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂)) :
-- imply
  BilinForm.IsNondegenerate' B₁ := by
-- proof
  rw [BilinForm.IsNondegenerate'] at h ⊢
  rw [Submodule.eq_bot_iff] at h ⊢
  intro v₁ hv₁
  have key : (v₁, (0 : V₂)) ∈ LinearMap.BilinForm.orthogonal
    (BilinForm.orthogonalSum B₁ B₂) ⊤ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro ⟨w₁, w₂⟩ _
    show (BilinForm.orthogonalSum B₁ B₂ ⟨w₁, w₂⟩) ⟨v₁, 0⟩ = 0
    simp only [BilinForm.orthogonalSum, LinearMap.mk₂_apply]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv₁
    have := hv₁ w₁ (Submodule.mem_top)
    unfold LinearMap.BilinForm.IsOrtho at this
    simp [this]
  have := h _ key
  exact Prod.mk.inj this |>.1


-- created on 2026-10-23
-- updated on 2026-10-26
