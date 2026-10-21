import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
private noncomputable def T (g : H →ₐ[k] k) : H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H g.toLinearMap ∘ₗ Coalgebra.comul
private lemma T_apply (g : H →ₐ[k] k) (h : H) :
    T g h = TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap (Coalgebra.comul (R := k) h)) := rfl
private lemma lid_map_eq (g : H →ₐ[k] k) (z : H ⊗[k] H) :
    Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) z) =
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add, ha, hb]
private noncomputable def Sₐ : H →ₐ[k] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])
@[simp] theorem Sₐ_apply (h : H) : Sₐ (k := k) h = HopfAlgebra.antipode k h := rfl
private lemma conv_apply (x y : H →ₐ[k] k) (h : H) :
    (WithConv.toConv x * WithConv.toConv y).ofConv h =
      LinearMap.mul' k k (TensorProduct.map x.toLinearMap y.toLinearMap (Coalgebra.comul (R := k) h)) := by
  rw [AlgHom.convMul_apply]
  induction (Coalgebra.comul (R := k) h) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, WithConv.ofConv_toConv]
  | add a b ha hb => simp only [map_add, ha, hb]
private lemma comp_T (x g : H →ₐ[k] k) (h : H) :
    x (T g h) = (WithConv.toConv g * WithConv.toConv x).ofConv h := by
  rw [conv_apply, T_apply]
  induction (Coalgebra.comul (R := k) h) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]
  | add a b ha hb => simp only [map_add, ha, hb]
private lemma convMul_compS_left (x : H →ₐ[k] k) :
    WithConv.toConv (x.comp Sₐ) * WithConv.toConv x = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H, LinearMap.mul' k k (TensorProduct.map (x.comp Sₐ).toLinearMap x.toLinearMap z) =
      x (LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.rTensor_tmul, map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
private lemma convMul_compS_right (x : H →ₐ[k] k) :
    WithConv.toConv x * WithConv.toConv (x.comp Sₐ) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H, LinearMap.mul' k k (TensorProduct.map x.toLinearMap (x.comp Sₐ).toLinearMap z) =
      x (LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.lTensor_tmul, map_mul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
private lemma exists_comp_T_eq (x y : H →ₐ[k] k) : ∃ g : H →ₐ[k] k, ∀ h, y h = x (T g h) := by
  refine ⟨(WithConv.toConv y * WithConv.toConv (x.comp Sₐ)).ofConv, fun h => ?_⟩
  rw [comp_T, WithConv.toConv_ofConv, mul_assoc, convMul_compS_left, mul_one, WithConv.ofConv_toConv]
private lemma comul_lid_rTensor (b : H →ₐ[k] k) (z : H ⊗[k] H) :
    Coalgebra.comul (R := k) (TensorProduct.lid k H (LinearMap.rTensor H b.toLinearMap z)) =
      TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (LinearMap.lTensor H (Coalgebra.comul (R := k)) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      LinearMap.lTensor_tmul]
  | add a c ha hc => simp only [map_add, ha, hc]
private lemma threefold (a b : H →ₐ[k] k) (w : (H ⊗[k] H) ⊗[k] H) :
    TensorProduct.lid k H (LinearMap.rTensor H a.toLinearMap
      (TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (TensorProduct.assoc k H H H w)))) =
    TensorProduct.lid k H (LinearMap.rTensor H
      (LinearMap.mul' k k ∘ₗ TensorProduct.map b.toLinearMap a.toLinearMap) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z c =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | tmul u v =>
      simp only [TensorProduct.assoc_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        AlgHom.toLinearMap_apply, map_smul, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply, smul_smul, mul_comm (b u) (a v)]
    | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
private lemma rTensor_conv (a b : H →ₐ[k] k) (w : H ⊗[k] H) :
    LinearMap.rTensor H (WithConv.toConv b * WithConv.toConv a).ofConv.toLinearMap w =
      LinearMap.rTensor H (LinearMap.mul' k k ∘ₗ TensorProduct.map b.toLinearMap a.toLinearMap)
        (LinearMap.rTensor H (Coalgebra.comul (R := k)) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c h =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, conv_apply, LinearMap.comp_apply]
  | add a c ha hc => simp only [map_add, ha, hc]
private lemma T_T (a b : H →ₐ[k] k) (h : H) :
    T a (T b h) = T (WithConv.toConv b * WithConv.toConv a).ofConv h := by
  rw [T_apply, T_apply, T_apply, comul_lid_rTensor, ← Coalgebra.coassoc_apply, threefold, rTensor_conv]
private lemma T_one (h : H) : T (1 : WithConv (H →ₐ[k] k)).ofConv h = h := by
  rw [T_apply]
  have : LinearMap.rTensor H (WithConv.ofConv (1 : WithConv (H →ₐ[k] k))).toLinearMap
      (Coalgebra.comul (R := k) h) =
      LinearMap.rTensor H (Coalgebra.counit (R := k) (A := H)) (Coalgebra.comul (R := k) h) := by
    induction (Coalgebra.comul (R := k) h) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c x =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.convOne_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add a c ha hc => simp only [map_add, ha, hc]
  rw [this, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
private lemma T_bijective (g : H →ₐ[k] k) : Function.Bijective (T g) := by
  have h1 : ∀ h, T (g.comp Sₐ) (T g h) = h := fun h => by
    rw [T_T, convMul_compS_right, T_one]
  have h2 : ∀ h, T g (T (g.comp Sₐ) h) = h := fun h => by
    rw [T_T, convMul_compS_left, T_one]
  exact ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun b => ⟨T (g.comp Sₐ) b, h2 b⟩⟩
private lemma T_mem (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (g : H →ₐ[k] k) (x : H) (hx : x ∈ K) : T g x ∈ K := by
  rw [T_apply]
  have hsub : ∀ z ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
      TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) ∈ K := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ht
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply]
      exact K.smul_mem hb _
    | zero => simp only [map_zero]; exact K.zero_mem
    | add a b _ _ ha hb => simp only [map_add]; exact K.add_mem ha hb
    | smul c a _ ha => simp only [map_smul]; exact K.smul_mem ha c
  exact hsub _ (hΔ x hx)
/--
[HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean)
-/
@[path]
private lemma main
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (τ : (H →ₐ[k] k) → (H →ₐ[k] H))
    (hτ : ∀ (g : H →ₐ[k] k) (h : H),
      τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h))) :
    (∀ g, Function.Bijective (τ g)) ∧
    (∀ (K : Subalgebra k H),
      (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
      ∀ g, ∀ x ∈ K, τ g x ∈ K) ∧
    (∀ x y : H →ₐ[k] k, ∃ g : H →ₐ[k] k, y = x.comp (τ g)) := by
  have hT : ∀ g h, τ g h = T g h := fun g h => by rw [hτ, lid_map_eq, T_apply]
  have hTf : ∀ g, (τ g : H → H) = T g := fun g => funext (hT g)
  refine ⟨fun g => ?_, fun K hΔ g x hx => ?_, fun x y => ?_⟩
  · rw [hTf]; exact T_bijective g
  · rw [hT]; exact T_mem K hΔ g x hx
  · obtain ⟨g, hg⟩ := exists_comp_T_eq x y
    exact ⟨g, AlgHom.ext fun h => by rw [AlgHom.comp_apply, hT]; exact hg h⟩

-- created on 2026-10-20
