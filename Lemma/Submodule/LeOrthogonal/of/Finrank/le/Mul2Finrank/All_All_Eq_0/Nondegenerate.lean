import Mathlib
import Initialize.Tactic.Attr.Basic
open Module FiniteDimensional


/--
[orthogonal_le_of_isotropic_of_finrank_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/MaximalIsotropicHelper.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
  {W₁ : Submodule k V}
-- given
  (hB_nd : B.Nondegenerate)
  (hW₁_iso : ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₁, B w₁ w₂ = 0)
  (hW₁_dim : finrank k V ≤ 2 * finrank k W₁) :
-- imply
  B.orthogonal W₁ ≤ W₁ := by
-- proof
  have hW₁_le_orth : W₁ ≤ B.orthogonal W₁ := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    apply hW₁_iso w hw v hv
  have h_orth_dim : finrank k (B.orthogonal W₁) = finrank k V - finrank k W₁ :=
    LinearMap.BilinForm.finrank_orthogonal hB_nd W₁
  have h_orth_le_W₁ : finrank k (B.orthogonal W₁) ≤ finrank k W₁ := by
    have hle : finrank k W₁ ≤ finrank k V := Submodule.finrank_le W₁
    omega
  have heq : W₁ = B.orthogonal W₁ :=
    Submodule.eq_of_le_of_finrank_le hW₁_le_orth h_orth_le_W₁
  rw [← heq]


-- created on 2026-10-23
-- updated on 2026-10-26
