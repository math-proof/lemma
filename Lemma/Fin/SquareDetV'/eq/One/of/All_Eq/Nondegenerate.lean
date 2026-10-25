import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part5
open Oriflamme


/--
[isometry_det_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
@[path]
private lemma main
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {g : V' ≃ₗ[k'] V'}
-- given
  (hnd : B'.Nondegenerate)
  (hiso : ∀ v w, B' (g v) (g w) = B' v w) :
-- imply
  ((g : V' →ₗ[k'] V').det) ^ 2 = 1 := by
-- proof
  set b := Module.Free.chooseBasis k' V'
  set Q := LinearMap.BilinForm.toMatrix b B'
  set M := LinearMap.toMatrix b b (g : V' →ₗ[k'] V')
  have hcomp : B'.comp (↑g) (↑g) = B' := by
    ext v w; simp [LinearMap.BilinForm.comp_apply, hiso]
  have hmat : Q = M.transpose * Q * M := by
    have := LinearMap.BilinForm.toMatrix_comp b b B' (↑g) (↑g)
    rw [hcomp] at this; exact this
  have hQdet : Q.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  rw [show (g : V' →ₗ[k'] V').det = M.det from by simp [M, LinearMap.det_toMatrix]]
  have h1 : Q.det = (M.transpose * Q * M).det := congr_arg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (M.det ^ 2 - 1) * Q.det = 0 := by
    have := sub_eq_zero.mpr h1.symm; ring_nf; ring_nf at this; exact this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).elim id (absurd · hQdet))



/--
[isometry_det_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma isometry_det_eq_one_or_neg_one
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {g : V' ≃ₗ[k'] V'}
-- given
  (hnd : B'.Nondegenerate)
  (hiso : ∀ v w, B' (g v) (g w) = B' v w) :
-- imply
  (g : V' →ₗ[k'] V').det = 1 ∨ (g : V' →ₗ[k'] V').det = -1 := by
-- proof
  have h := isometry_det_sq_eq_one B' hnd g hiso
  have h1 := sub_eq_zero.mpr h
  have h2 : ((g : V' →ₗ[k'] V').det - 1) * ((g : V' →ₗ[k'] V').det + 1) = 0 := by
    ring_nf; ring_nf at h1; exact h1
  obtain h3 | h4 := mul_eq_zero.mp h2
  · left; exact sub_eq_zero.mp h3
  · right; exact eq_neg_of_add_eq_zero_left h4



/--
[hyp_swap_det_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma hyp_swap_det_neg_one
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k'] :
-- imply
  Matrix.det (!![0, (1 : k'); 1, 0]) = -1 := by
-- proof
  rw [Matrix.det_fin_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]



/--
[hyp_plane_swap_isometry_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma hyp_plane_swap_isometry_det
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  {e₁ e₂ : Fin 2 → k'}
  {b : Module.Basis (Fin 2) k' (Fin 2 → k')}
  {g : (Fin 2 → k') ≃ₗ[k'] (Fin 2 → k')}
  {a : k'}
-- given
  (hb1 : b 0 = e₁)
  (hb2 : b 1 = e₂)
  (ha : a ≠ 0)
  (hge1 : g e₁ = a • e₂)
  (hge2 : g e₂ = a⁻¹ • e₁) :
-- imply
  (g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')).det = -1 := by
-- proof
  rw [show (g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')).det =
    (LinearMap.toMatrix b b (↑g)).det from by simp [LinearMap.det_toMatrix]]
  have hge1' : (↑g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')) (b 0) = a • b 1 := by
    simp [hb1, hb2, hge1, LinearEquiv.coe_coe]
  have hge2' : (↑g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')) (b 1) = a⁻¹ • b 0 := by
    simp [hb1, hb2, hge2, LinearEquiv.coe_coe]
  have hM : LinearMap.toMatrix b b (↑g) = !![0, a⁻¹; a, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hge1', hge2', Module.Basis.repr_self,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  rw [hM, Matrix.det_fin_two]; simp; exact inv_mul_cancel₀ ha
section DistinctOrbits
variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
  [FiniteDimensional k' V']



/--
[extend_auto_to_SO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma extend_auto_to_SO
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {n : ℕ}
  {W₁ W₂ Y : Submodule k' V'}
  {g : V' ≃ₗ[k'] V'}
-- given
  (hnd : B'.Nondegenerate)
  (hY_le_W₁ : Y ≤ W₁)
  (hY_le_W₂ : Y ≤ W₂)
  (hY_dim : Module.finrank k' Y = n - 1)
  (hW₁_dim : Module.finrank k' W₁ = n)
  (hg_isom : ∀ v w, B' (g v) (g w) = B' v w)
  (hg_onto : Submodule.map g.toLinearMap W₁ = W₂) :
-- imply
  ∃ h : V' ≃ₗ[k'] V', (∀ v ∈ Y, h (g v) = v) ∧ Submodule.map h.toLinearMap W₂ = W₂ ∧ (∀ v w, B' (h v) (h w) = B' v w) ∧ (h : V' →ₗ[k'] V').det = 1 :=
-- proof
witt_extension_preserves_W₂ B' hnd n W₁ W₂ Y hY_le_W₁ hY_le_W₂ hY_dim hW₁_dim g hg_isom hg_onto



/--
[witt_adjust_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma witt_adjust_isometry
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {n : ℕ}
  {Y : Submodule k' V'}
  {V₁ V₂ : Submodule k' V'}
  {g : V' ≃ₗ[k'] V'}
-- given
  (hnd : B'.Nondegenerate)
  (hY_iso : IsTotallyIsotropic k' V' B' Y)
  (hY_dim : Module.finrank k' Y = n - 1)
  (hV₁_iso : IsTotallyIsotropic k' V' B' V₁)
  (hV₁_dim : Module.finrank k' V₁ = n)
  (hV₁_sub : V₁ ≤ B'.orthogonal Y)
  (hY_le_V₁ : Y ≤ V₁)
  (hV₂_iso : IsTotallyIsotropic k' V' B' V₂)
  (hV₂_dim : Module.finrank k' V₂ = n)
  (hV₂_sub : V₂ ≤ B'.orthogonal Y)
  (hY_le_V₂ : Y ≤ V₂)
  (hV₁₂ : V₁ ≠ V₂)
  (hiso : ∀ v w, B' (g v) (g w) = B' v w)
  (hmaps : V₁.map (g : V' →ₗ[k'] V') = V₂) :
-- imply
  ∃ g' : V' ≃ₗ[k'] V', (∀ v w, B' (g' v) (g' w) = B' v w) ∧ V₁.map (g' : V' →ₗ[k'] V') = V₂ ∧ (∀ v ∈ Y, g' v = v) ∧ (g' : V' →ₗ[k'] V').det = (g : V' →ₗ[k'] V').det := by
-- proof
  obtain ⟨h, h_undo_g, h_pres_V₂, h_isom, h_det⟩ :=
    extend_auto_to_SO B' hnd n V₁ V₂ Y hY_le_V₁ hY_le_V₂ hY_dim hV₁_dim g hiso hmaps
  refine ⟨g.trans h, ?_, ?_, ?_, ?_⟩
  ·
    intro u v
    simp only [LinearEquiv.trans_apply]
    rw [h_isom, hiso]
  ·
    have htrans : ((g.trans h) : V' →ₗ[k'] V') = h.toLinearMap ∘ₗ g.toLinearMap := by
      ext x; simp [LinearEquiv.trans_apply]
    rw [htrans, Submodule.map_comp, hmaps, h_pres_V₂]
  ·
    intro v hv
    simp only [LinearEquiv.trans_apply]
    exact h_undo_g v hv
  ·
    have htrans : ((g.trans h) : V' →ₗ[k'] V') = h.toLinearMap ∘ₗ g.toLinearMap := by
      ext x; simp [LinearEquiv.trans_apply]
    rw [htrans, LinearMap.det_comp, h_det, one_mul]



/--
[det_quotient_VmodYperp_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma det_quotient_VmodYperp_eq_one
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {Y : Submodule k' V'}
  {g' : V' ≃ₗ[k'] V'}
-- given
  (_hnd : B'.Nondegenerate)
  (hiso' : ∀ v w, B' (g' v) (g' w) = B' v w)
  (hfix : ∀ v ∈ Y, g' v = v)
  (he' : B'.orthogonal Y ≤ Submodule.comap (g' : V' →ₗ[k'] V') (B'.orthogonal Y)) :
-- imply
  LinearMap.det ((B'.orthogonal Y).mapQ (B'.orthogonal Y) (g' : V' →ₗ[k'] V') he') = 1 := by
-- proof
  suffices h : (B'.orthogonal Y).mapQ (B'.orthogonal Y) (g' : V' →ₗ[k'] V') he' = LinearMap.id by
    rw [h, LinearMap.det_id]
  ext v
  simp only [LinearMap.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  unfold LinearMap.BilinForm.IsOrtho
  have h2 : g'.symm w = w := (LinearEquiv.symm_apply_eq g').mpr (hfix w hw).symm
  have h3 : (B' w) ((g' : V' →ₗ[k'] V') v) = (B' w) v := by
    show (B' w) (g' v) = (B' w) v
    calc (B' w) (g' v)
      = (B' (g' (g'.symm w))) (g' v) := by rw [g'.apply_symm_apply]
      _ = (B' (g'.symm w)) v := hiso' _ _
      _ = (B' w) v := by rw [h2]
  simp only [map_sub, h3, sub_self]



/--
[det_quotient_YperpmodY_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma det_quotient_YperpmodY_eq_neg_one
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {n : ℕ}
  {Y : Submodule k' V'}
  {V₁ V₂ : Submodule k' V'}
  {g' : V' ≃ₗ[k'] V'}
-- given
  (hnd : B'.Nondegenerate)
  (hY_iso : IsTotallyIsotropic k' V' B' Y)
  (hY_dim : Module.finrank k' Y = n - 1)
  (hV₁_sub : V₁ ≤ B'.orthogonal Y)
  (hY_le_V₁ : Y ≤ V₁)
  (hV₂_sub : V₂ ≤ B'.orthogonal Y)
  (hY_le_V₂ : Y ≤ V₂)
  (hV₁₂ : V₁ ≠ V₂)
  (hiso' : ∀ v w, B' (g' v) (g' w) = B' v w)
  (hmaps' : V₁.map (g' : V' →ₗ[k'] V') = V₂)
  (hfix : ∀ v ∈ Y, g' v = v)
  (he : Y ≤ Submodule.comap (g' : V' →ₗ[k'] V') Y)
  (he' : B'.orthogonal Y ≤ Submodule.comap (g' : V' →ₗ[k'] V') (B'.orthogonal Y))
  (he_inner : Y.comap (B'.orthogonal Y).subtype ≤ Submodule.comap ((g' : V' →ₗ[k'] V').restrict he') (Y.comap (B'.orthogonal Y).subtype))
  (hswap_basis : ∃ (b : Module.Basis (Fin 2) k' (↥(B'.orthogonal Y) ⧸ Y.comap (B'.orthogonal Y).subtype)) (a : k'), a ≠ 0 ∧ ((Y.comap (B'.orthogonal Y).subtype).mapQ (Y.comap (B'.orthogonal Y).subtype) ((g' : V' →ₗ[k'] V').restrict he') he_inner) (b 0) = a • b 1 ∧ ((Y.comap (B'.orthogonal Y).subtype).mapQ (Y.comap (B'.orthogonal Y).subtype) ((g' : V' →ₗ[k'] V').restrict he') he_inner) (b 1) = a⁻¹ • b 0) :
-- imply
  LinearMap.det ((Y.comap (B'.orthogonal Y).subtype).mapQ (Y.comap (B'.orthogonal Y).subtype) ((g' : V' →ₗ[k'] V').restrict he') he_inner) = -1 := by
-- proof
  obtain ⟨b, a, ha, h0, h1⟩ := hswap_basis
  set f := (Y.comap (B'.orthogonal Y).subtype).mapQ
    (Y.comap (B'.orthogonal Y).subtype)
    ((g' : V' →ₗ[k'] V').restrict he') he_inner with hf_def
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b f = !![0, a⁻¹; a, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, h0, h1, Module.Basis.repr_self]
  rw [hM, Matrix.det_fin_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  exact mul_inv_cancel₀ ha
/-- Combines the three filtration pieces $(Y, Y^\perp/Y, V/Y^\perp)$ to compute
$\det(g'|_{V/Y}) = -1$ for an isometry swapping the two distinct maximal isotropic subspaces. -/
section TwoOrbits
variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
  [FiniteDimensional k' V']



/--
[exactly_two_SO_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean)
-/
private lemma exactly_two_SO_orbits
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Field k']
  [AddCommGroup V']
  [Module k' V']
  {B' : LinearMap.BilinForm k' V'}
  {n : ℕ}
  {V_plus V_minus : Submodule k' V'}
  {Y₀ : Submodule k' V'}
-- given
  (hVp_ti : IsTotallyIsotropic k' V' B' V_plus)
  (hVp_dim : Module.finrank k' V_plus = n)
  (hVm_ti : IsTotallyIsotropic k' V' B' V_minus)
  (hVm_dim : Module.finrank k' V_minus = n)
  (hVpm_ne : V_plus ≠ V_minus)
  (_hY₀_ti : IsTotallyIsotropic k' V' B' Y₀)
  (hY₀_dim : Module.finrank k' Y₀ = n - 1)
  (_hY₀_Vp : Y₀ ≤ V_plus)
  (_hY₀_Vm : Y₀ ≤ V_minus)
  (prop1_transported : ∀ g ∈ SpecialIsometryGroup B', ∀ W : Submodule k' V', IsTotallyIsotropic k' V' B' W → Module.finrank k' W = n → Submodule.map (g : V' →ₗ[k'] V') Y₀ ≤ W → W = Submodule.map (g : V' →ₗ[k'] V') V_plus ∨ W = Submodule.map (g : V' →ₗ[k'] V') V_minus)
  (so_transitive_codim1 : ∀ Y₁ Y₂ : Submodule k' V', IsTotallyIsotropic k' V' B' Y₁ → Module.finrank k' Y₁ = n - 1 → IsTotallyIsotropic k' V' B' Y₂ → Module.finrank k' Y₂ = n - 1 → ∃ g ∈ SpecialIsometryGroup B', Submodule.map (g : V' →ₗ[k'] V') Y₁ = Y₂)
  (contains_codim1 : ∀ W : Submodule k' V', IsTotallyIsotropic k' V' B' W → Module.finrank k' W = n → ∃ Y : Submodule k' V', IsTotallyIsotropic k' V' B' Y ∧ Module.finrank k' Y = n - 1 ∧ Y ≤ W) :
-- imply
  ∀ W : Submodule k' V', IsTotallyIsotropic k' V' B' W → Module.finrank k' W = n → (∃ g ∈ SpecialIsometryGroup B', Submodule.map (g : V' →ₗ[k'] V') V_plus = W) ∨ (∃ g ∈ SpecialIsometryGroup B', Submodule.map (g : V' →ₗ[k'] V') V_minus = W) := by
-- proof
  intro W hW_ti hW_dim
  obtain ⟨Y_W, hYw_ti, hYw_dim, hYw_le⟩ := contains_codim1 W hW_ti hW_dim
  obtain ⟨g, hg_SO, hg_maps⟩ :=
    so_transitive_codim1 Y₀ Y_W _hY₀_ti hY₀_dim hYw_ti hYw_dim
  have hYw_le_W : Submodule.map (g : V' →ₗ[k'] V') Y₀ ≤ W := hg_maps ▸ hYw_le
  obtain h | h := prop1_transported g hg_SO W hW_ti hW_dim hYw_le_W
  · left; exact ⟨g, hg_SO, h.symm⟩
  · right; exact ⟨g, hg_SO, h.symm⟩
section DistinctOrbitClasses
variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
  [FiniteDimensional k' V']
/-- The two oriflamme orbit classes are disjoint: no maximal isotropic subspace lies in both
orbit classes simultaneously, since otherwise an $\mathrm{SO}$-element would identify the two
distinguished types $V_1$ and $V_2$, contradicting `distinct_SO_orbits`. -/



-- created on 2026-10-23
-- updated on 2026-10-24
