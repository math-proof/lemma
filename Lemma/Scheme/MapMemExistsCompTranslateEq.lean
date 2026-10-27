import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private noncomputable def T {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H] (g : H →ₐ[k] k) : H →ₗ[k] H :=
  LinearMap.comp (TensorProduct.lid k H).toLinearMap
    (LinearMap.comp (LinearMap.rTensor H g.toLinearMap) Coalgebra.comul)

private noncomputable def Sₐ {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H] : H →ₐ[k] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul_antidistrib, mul_comm])

@[simp] private lemma Sₐ_apply {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H] (h : H) : Sₐ (k := k) h = HopfAlgebra.antipode k h := rfl

private lemma T_apply
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (g : H →ₐ[k] k)
  (h : H) :
  -- imply
  T g h = TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap (Coalgebra.comul (R := k) h)) :=
  rfl

private lemma lid_map_eq
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (g : H →ₐ[k] k)
  (z : H ⊗[k] H) :
  -- imply
  Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) z) =
    TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) := by
  -- proof
  refine TensorProduct.inductionOn z ?_ ?_
  ·
    intro a b
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, AlgHom.coe_id, id_eq]
  ·
    intro a b ha hb
    simp only [map_add, ha, hb]

private lemma conv_apply
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (x y : H →ₐ[k] k)
  (h : H) :
  -- imply
  (WithConv.toConv x * WithConv.toConv y).ofConv h =
    LinearMap.mul' k k (TensorProduct.map x.toLinearMap y.toLinearMap (Coalgebra.comul (R := k) h)) := by
  -- proof
  rw [AlgHom.convMul_apply]
  refine TensorProduct.inductionOn (Coalgebra.comul (R := k) h) ?_ ?_
  ·
    intro a b
    simp only [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply]
  ·
    intro a b ha hb
    simp only [map_add, ha, hb]

private lemma comp_T
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (x g : H →ₐ[k] k)
  (h : H) :
  -- imply
  x (T g h) = (WithConv.toConv g * WithConv.toConv x).ofConv h := by
  -- proof
  rw [conv_apply, T_apply]
  refine TensorProduct.inductionOn (Coalgebra.comul (R := k) h) ?_ ?_
  ·
    intro a b
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]
  ·
    intro a b ha hb
    simp only [map_add, ha, hb]

private lemma convMul_compS_left
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (x : H →ₐ[k] k) :
  -- imply
  WithConv.toConv (x.comp Sₐ) * WithConv.toConv x = 1 := by
  -- proof
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H, LinearMap.mul' k k (TensorProduct.map (x.comp Sₐ).toLinearMap x.toLinearMap z) = x (LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro a b
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.rTensor_tmul, map_mul]
    ·
      intro a b ha hb
      simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

private lemma convMul_compS_right
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (x : H →ₐ[k] k) :
  -- imply
  WithConv.toConv x * WithConv.toConv (x.comp Sₐ) = 1 := by
  -- proof
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [conv_apply, AlgHom.convOne_apply]
  have key : ∀ z : H ⊗[k] H, LinearMap.mul' k k (TensorProduct.map x.toLinearMap (x.comp Sₐ).toLinearMap z) = x (LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k) z)) := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro a b
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        Sₐ_apply, LinearMap.lTensor_tmul, map_mul]
    ·
      intro a b ha hb
      simp only [map_add, ha, hb]
  rw [key, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

private lemma exists_comp_T_eq
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (x y : H →ₐ[k] k) :
  -- imply
  ∃ g : H →ₐ[k] k, ∀ h, y h = x (T g h) := by
  -- proof
  refine ⟨(WithConv.toConv y * WithConv.toConv (x.comp Sₐ)).ofConv, fun h => ?_⟩
  rw [comp_T, WithConv.toConv_ofConv, mul_assoc, convMul_compS_left, mul_one, WithConv.ofConv_toConv]

private lemma comul_lid_rTensor
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (b : H →ₐ[k] k)
  (z : H ⊗[k] H) :
  -- imply
  Coalgebra.comul (R := k) (TensorProduct.lid k H (LinearMap.rTensor H b.toLinearMap z)) =
    TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
      (LinearMap.lTensor H (Coalgebra.comul (R := k)) z)) := by
  -- proof
  refine TensorProduct.inductionOn z ?_ ?_
  ·
    intro c h
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply, map_smul,
      LinearMap.lTensor_tmul]
  ·
    intro a c ha hc
    simp only [map_add, ha, hc]

private lemma threefold
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (a b : H →ₐ[k] k)
  (w : (H ⊗[k] H) ⊗[k] H) :
  -- imply
  TensorProduct.lid k H (LinearMap.rTensor H a.toLinearMap
      (TensorProduct.lid k (H ⊗[k] H) (LinearMap.rTensor (H ⊗[k] H) b.toLinearMap
        (TensorProduct.assoc k H H H w)))) =
    TensorProduct.lid k H (LinearMap.rTensor H
      (LinearMap.comp (LinearMap.mul' k k) (TensorProduct.map b.toLinearMap a.toLinearMap)) w) := by
  -- proof
  refine TensorProduct.inductionOn w ?_ ?_
  ·
    intro z c
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro u v
      simp only [TensorProduct.assoc_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        AlgHom.toLinearMap_apply, map_smul, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.mul'_apply, smul_smul, mul_comm (b u) (a v)]
    ·
      intro z₁ z₂ h₁ h₂
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  ·
    intro w₁ w₂ h₁ h₂
    simp only [map_add, h₁, h₂]

private lemma rTensor_conv
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (a b : H →ₐ[k] k)
  (w : H ⊗[k] H) :
  -- imply
  LinearMap.rTensor H (WithConv.toConv b * WithConv.toConv a).ofConv.toLinearMap w =
    LinearMap.rTensor H (LinearMap.comp (LinearMap.mul' k k) (TensorProduct.map b.toLinearMap a.toLinearMap))
      (LinearMap.rTensor H (Coalgebra.comul (R := k)) w) := by
  -- proof
  refine TensorProduct.inductionOn w ?_ ?_
  ·
    intro c h
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, conv_apply, LinearMap.comp_apply]
  ·
    intro a c ha hc
    simp only [map_add, ha, hc]

private lemma T_T
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (a b : H →ₐ[k] k)
  (h : H) :
  -- imply
  T a (T b h) = T (WithConv.toConv b * WithConv.toConv a).ofConv h := by
  -- proof
  rw [T_apply, T_apply, T_apply, comul_lid_rTensor, ← Coalgebra.coassoc_apply, threefold, rTensor_conv]

private lemma T_one
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (h : H) :
  -- imply
  T (1 : WithConv (H →ₐ[k] k)).ofConv h = h := by
  -- proof
  rw [T_apply]
  have : LinearMap.rTensor H (WithConv.ofConv (1 : WithConv (H →ₐ[k] k))).toLinearMap (Coalgebra.comul (R := k) h) = LinearMap.rTensor H (Coalgebra.counit (R := k) (A := H)) (Coalgebra.comul (R := k) h) := by
    refine TensorProduct.inductionOn (Coalgebra.comul (R := k) h) ?_ ?_
    ·
      intro c x
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.convOne_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    ·
      intro a c ha hc
      simp only [map_add, ha, hc]
  rw [this, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

private lemma T_bijective
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (g : H →ₐ[k] k) :
  -- imply
  Function.Bijective (T g) := by
  -- proof
  have h1 : ∀ h, T (g.comp Sₐ) (T g h) = h := fun h => by
    rw [T_T, convMul_compS_right, T_one]
  have h2 : ∀ h, T g (T (g.comp Sₐ) h) = h := fun h => by
    rw [T_T, convMul_compS_left, T_one]
  refine ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun b => ⟨T (g.comp Sₐ) b, h2 b⟩⟩

private lemma T_mem
  {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H]
  (K : Subalgebra k H)
  (g : H →ₐ[k] k)
  (x : H)
  -- given
  (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
  (hx : x ∈ K) :
  -- imply
  T g x ∈ K := by
  -- proof
  rw [T_apply]
  suffices hsub : ∀ z ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}, TensorProduct.lid k H (LinearMap.rTensor H g.toLinearMap z) ∈ K by
    apply hsub _ (hΔ x hx)
  intro z hz
  refine Submodule.span_induction (fun t ht => ?_) ?_ (fun a b _ _ ha hb => ?_) (fun c t _ ha => ?_) hz
  ·
    obtain ⟨a, h⟩ := ht
    obtain ⟨ha, h⟩ := h
    obtain ⟨b, h⟩ := h
    obtain ⟨hb, h⟩ := h
    rw [h]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply]
    apply K.smul_mem hb _
  ·
    simp only [map_zero]
    apply K.zero_mem
  ·
    simp only [map_add]
    apply K.add_mem ha hb
  ·
    simp only [map_smul]
    apply K.smul_mem ha c

/--
[HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_bijective_translate_and_map_mem_and_exists_comp_translate_eq.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {H : Type v} [CommRing H] [HopfAlgebra k H]
  (τ : (H →ₐ[k] k) → (H →ₐ[k] H))
  -- given
  (hτ : ∀ (g : H →ₐ[k] k) (h : H), τ g h = Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map g (AlgHom.id k H) (Coalgebra.comul h))) :
  -- imply
  (∀ g, Function.Bijective (τ g)) ∧ (∀ (K : Subalgebra k H), (∀ x ∈ K, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) → ∀ g, ∀ x ∈ K, τ g x ∈ K) ∧ (∀ x y : H →ₐ[k] k, ∃ g : H →ₐ[k] k, y = x.comp (τ g)) := by
  -- proof
  have hT : ∀ g h, τ g h = T g h := fun g h => by
    rw [hτ, lid_map_eq, T_apply]
  have hTf : ∀ g, (τ g : H → H) = T g := fun g => funext (hT g)
  refine ⟨fun g => ?_, fun K hΔ g x hx => ?_, fun x y => ?_⟩
  ·
    rw [hTf]
    apply T_bijective g
  ·
    rw [hT]
    apply T_mem K g x hΔ hx
  ·
    obtain ⟨g, hg⟩ := exists_comp_T_eq x y
    refine ⟨g, AlgHom.ext fun h => ?_⟩
    rw [AlgHom.comp_apply, hT]
    apply hg h


-- created on 2026-10-20
