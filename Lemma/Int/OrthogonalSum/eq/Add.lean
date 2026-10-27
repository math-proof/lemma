import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
open Garrett


namespace Garrett

/--
[BilinForm.orthogonalSum_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma BilinForm.orthogonalSum_apply
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂}
  {v w : V₁ × V₂} :
-- imply
  BilinForm.orthogonalSum B₁ B₂ v w = B₁ v.1 w.1 + B₂ v.2 w.2 := by
-- proof
  simp [BilinForm.orthogonalSum, LinearMap.mk₂]

end Garrett

namespace Garrett

/--
[neg_orthogonalSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma neg_orthogonalSum_eq
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂} :
-- imply
  -(BilinForm.orthogonalSum B₁ B₂) = BilinForm.orthogonalSum (-B₁) (-B₂) := by
-- proof
  ext v w
  all_goals simp [BilinForm.orthogonalSum, LinearMap.mk₂, LinearMap.neg_apply, map_zero,
    LinearMap.zero_apply]

end Garrett

namespace Garrett

/--
[orthogonalSum_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma orthogonalSum_nondegenerate
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂}
-- given
  (h₁ : BilinForm.IsNondegenerate' B₁)
  (h₂ : BilinForm.IsNondegenerate' B₂) :
-- imply
  BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂) := by
-- proof
  rw [BilinForm.IsNondegenerate'] at *; rw [Submodule.eq_bot_iff] at *
  intro ⟨v₁, v₂⟩ hv; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
  have hv1 : v₁ = 0 := by
    apply h₁; rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro w _
    have := hv (w, 0) Submodule.mem_top
    unfold LinearMap.BilinForm.IsOrtho at this; simp at this; exact this
  have hv2 : v₂ = 0 := by
    apply h₂; rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro w _
    have := hv (0, w) Submodule.mem_top
    unfold LinearMap.BilinForm.IsOrtho at this; simp at this; exact this
  simp [hv1, hv2]

end Garrett

namespace Garrett

/--
[neg_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma neg_nondegenerate
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hnd : BilinForm.IsNondegenerate' B) :
-- imply
  BilinForm.IsNondegenerate' (-B) := by
-- proof
  rw [BilinForm.IsNondegenerate'] at *; rw [Submodule.eq_bot_iff] at *
  intro v hv; apply hnd; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro w hw; have := hv w hw
  unfold LinearMap.BilinForm.IsOrtho at this ⊢; simp at this; exact this

end Garrett

namespace Garrett

/--
[directSum_neg_isHyperbolic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma directSum_neg_isHyperbolic
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hnd : BilinForm.IsNondegenerate' B) :
-- imply
  BilinForm.IsHyperbolic (BilinForm.orthogonalSum B (-B)) := by
-- proof
  refine ⟨diagonal V, ?_, ?_, ?_⟩
  ·
    intro ⟨w₁, w₂⟩ (hw : w₁ = w₂) ⟨u₁, u₂⟩ (hu : u₁ = u₂)
    simp [hw, hu]
  ·
    ext ⟨a, b⟩
    simp only [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro ha
      show a = b
      have hab : a - b = 0 := by
        rw [BilinForm.IsNondegenerate'] at hnd
        rw [Submodule.eq_bot_iff] at hnd
        apply hnd
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro w _
        unfold LinearMap.BilinForm.IsOrtho
        have h := ha (w, w) (show (w : V) = w from rfl)
        unfold LinearMap.BilinForm.IsOrtho at h
        simp at h
        rw [map_sub, add_neg_eq_zero.mp h, sub_self]
      exact sub_eq_zero.mp hab
    · intro (ha : a = b) ⟨w₁, w₂⟩ (hw : w₁ = w₂)
      unfold LinearMap.BilinForm.IsOrtho
      simp [ha, hw]
  · exact orthogonalSum_nondegenerate B (-B) hnd (neg_nondegenerate B hnd)

end Garrett

namespace Garrett

/--
[nondegenerate_fst_of_orthogonalSum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma nondegenerate_fst_of_orthogonalSum
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂}
-- given
  (hnd : BilinForm.IsNondegenerate' (BilinForm.orthogonalSum B₁ B₂)) :
-- imply
  BilinForm.IsNondegenerate' B₁ := by
-- proof
  rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at hnd ⊢
  intro v₁ hv₁
  have : (v₁, (0 : V₂)) = (0 : V₁ × V₂) := by
    apply hnd
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro ⟨w₁, w₂⟩ _
    unfold LinearMap.BilinForm.IsOrtho
    simp only [BilinForm.orthogonalSum_apply, map_zero, add_zero]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv₁
    exact hv₁ w₁ Submodule.mem_top
  exact Prod.mk.inj this |>.1

end Garrett

namespace Garrett

/--
[lagrangian_W1_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma lagrangian_W1_isotropic
  [Field k]
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [FiniteDimensional k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  [FiniteDimensional k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂}
  {W₁₂ : Submodule k (V₁ × V₂)}
  {W₂ : Submodule k V₂}
-- given
  (hW₁₂_iso : ∀ w₁ ∈ W₁₂, ∀ w₂ ∈ W₁₂, BilinForm.orthogonalSum B₁ B₂ w₁ w₂ = 0)
  (hW₂_iso : ∀ w₁ ∈ W₂, ∀ w₂ ∈ W₂, B₂ w₁ w₂ = 0) :
-- imply
  let W₁ := Submodule.map (LinearMap.fst k V₁ V₂) (W₁₂ ⊓ Submodule.prod ⊤ W₂) W₁ ≤ LinearMap.BilinForm.orthogonal B₁ W₁ := by
-- proof
  intro W₁ x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  unfold LinearMap.BilinForm.IsOrtho
  rw [Submodule.mem_map] at hx hy
  obtain ⟨⟨x₁, x₂⟩, hxm, rfl⟩ := hx
  obtain ⟨⟨y₁, y₂⟩, hym, rfl⟩ := hy
  simp only [LinearMap.fst_apply]
  simp only [Submodule.mem_inf, Submodule.mem_prod] at hxm hym
  have h1 := hW₁₂_iso (y₁, y₂) hym.1 (x₁, x₂) hxm.1
  simp only [BilinForm.orthogonalSum_apply] at h1
  have h2 := hW₂_iso y₂ hym.2.2 x₂ hxm.2.2
  rwa [h2, add_zero] at h1

end Garrett

namespace Garrett

/--
[IsNondegenerate'_to_Nondegenerate_inline](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma IsNondegenerate'_to_Nondegenerate_inline
  [Field k]
  [Field k₀]
  [AddCommGroup V]
  [Module k₀ V]
  [FiniteDimensional k₀ V]
  {B : LinearMap.BilinForm k₀ V}
-- given
  (h : BilinForm.IsNondegenerate' B) :
-- imply
  B.Nondegenerate := by
-- proof
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
  intro y hy
  rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at h
  exact h y (by rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro n _; exact hy n)

end Garrett

namespace Garrett

/--
[lagrangian_finrank_inline](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma lagrangian_finrank_inline
  [Field k]
  [Field k₀]
  [AddCommGroup V]
  [Module k₀ V]
  [FiniteDimensional k₀ V]
  {B : LinearMap.BilinForm k₀ V}
  {W : Submodule k₀ V}
-- given
  (hW_lagrangian : LinearMap.BilinForm.orthogonal B W = W)
  (hB_nd : BilinForm.IsNondegenerate' B) :
-- imply
  2 * Module.finrank k₀ W = Module.finrank k₀ V := by
-- proof
  have hB_nd' : B.Nondegenerate := IsNondegenerate'_to_Nondegenerate_inline hB_nd
  have h := LinearMap.BilinForm.finrank_orthogonal hB_nd' W
  rw [hW_lagrangian] at h
  omega

end Garrett

namespace Garrett

/--
[isHyperbolic_of_isometric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean)
-/
@[path]
private lemma isHyperbolic_of_isometric
  [Field k]
  [AddCommGroup V₁]
  [Module k V₁]
  [AddCommGroup V₂]
  [Module k V₂]
  {B₁ : LinearMap.BilinForm k V₁}
  {B₂ : LinearMap.BilinForm k V₂}
  {φ : V₁ ≃ₗ[k] V₂}
-- given
  (hiso : IsFormedSpaceIsometry B₁ B₂ φ)
  (hH : BilinForm.IsHyperbolic B₂) :
-- imply
  BilinForm.IsHyperbolic B₁ := by
-- proof
  obtain ⟨W₂, hW₂_iso, hW₂_orth, hnd₂⟩ := hH
  refine ⟨Submodule.comap φ.toLinearMap W₂, ?_, ?_, ?_⟩
  ·
    intro v₁ hv₁ v₂ hv₂
    rw [← hiso v₁ v₂]; exact hW₂_iso (φ v₁) hv₁ (φ v₂) hv₂
  ·
    ext v
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_comap,
      LinearEquiv.coe_toLinearMap]
    constructor
    · intro hv; rw [← hW₂_orth, LinearMap.BilinForm.mem_orthogonal_iff]
      intro w₂ hw₂; unfold LinearMap.BilinForm.IsOrtho
      obtain ⟨u, rfl⟩ := φ.surjective w₂; rw [hiso u v]; exact hv u hw₂
    · intro hv w hw; unfold LinearMap.BilinForm.IsOrtho; rw [← hiso w v]
      rw [← hW₂_orth] at hv; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
      exact hv (φ w) hw
  ·
    rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff]
    intro v hv
    have hφv : φ v = 0 := by
      rw [BilinForm.IsNondegenerate', Submodule.eq_bot_iff] at hnd₂; apply hnd₂
      rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro w _
      unfold LinearMap.BilinForm.IsOrtho; obtain ⟨u, rfl⟩ := φ.surjective w
      rw [hiso u v]; rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
      exact hv u Submodule.mem_top
    exact φ.injective (by rw [hφv, map_zero])
/-- Combination of cancellation and isometry-preservation: if `X ⊕ H₁` is
isometric to a hyperbolic space `H₂` and `H₁` is hyperbolic, then `X` is
hyperbolic. -/
variable {U X Y : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

end Garrett


-- created on 2026-10-23
-- updated on 2026-10-26
