import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Bialgebra k B]
abbrev augIdeal : Ideal B := RingHom.ker (Bialgebra.counitAlgHom k B)
abbrev Tan : Type _ :=
  {D : B →ₐ[k] DualNumber k // ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b}
variable {k B}
private lemma mem_augIdeal {b : B} : b ∈ augIdeal k B ↔ Bialgebra.counitAlgHom k B b = 0 := RingHom.mem_ker
private noncomputable def dLin (D : B →ₐ[k] DualNumber k) : B →ₗ[k] k :=
  (TrivSqZeroExt.sndHom k k).comp D.toLinearMap
@[simp] lemma dLin_apply (D : B →ₐ[k] DualNumber k) (b : B) : dLin D b = TrivSqZeroExt.snd (D b) := rfl
private noncomputable def dI (D : B →ₐ[k] DualNumber k) : ↥(augIdeal k B) →ₗ[k] k :=
  (dLin D).comp ((augIdeal k B).subtype.restrictScalars k)
@[simp] lemma dI_apply (D : B →ₐ[k] DualNumber k) (x : ↥(augIdeal k B)) :
    dI D x = TrivSqZeroExt.snd (D (x : B)) := rfl
private lemma dI_mul (D : Tan k B) (x y : ↥(augIdeal k B)) : dI D.1 (x * y) = 0 := by
  have hx : Bialgebra.counitAlgHom k B (x : B) = 0 := mem_augIdeal.mp x.2
  have hy : Bialgebra.counitAlgHom k B (y : B) = 0 := mem_augIdeal.mp y.2
  rw [dI_apply]
  have : ((x * y : ↥(augIdeal k B)) : B) = (x : B) * (y : B) := rfl
  rw [this, map_mul, DualNumber.snd_mul, D.2, D.2, hx, hy, zero_mul, mul_zero, add_zero]
private noncomputable def gamma (D : Tan k B) : (augIdeal k B).Cotangent →ₗ[k] k :=
  Ideal.Cotangent.lift (dI D.1) (dI_mul D)
@[simp] lemma gamma_toCotangent (D : Tan k B) (x : ↥(augIdeal k B)) :
    gamma D ((augIdeal k B).toCotangent x) = TrivSqZeroExt.snd (D.1 (x : B)) := by
  simp [gamma]
private noncomputable def proj : B →ₗ[k] ↥(augIdeal k B) where
  toFun b := ⟨b - algebraMap k B (Bialgebra.counitAlgHom k B b), by
    rw [mem_augIdeal, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]⟩
  map_add' a b := by
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' r b := by
    ext
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, map_mul, Algebra.smul_def,
      AlgHom.commutes, Algebra.algebraMap_self_apply]
    ring
@[simp] lemma coe_proj (b : B) :
    (proj (k := k) b : B) = b - algebraMap k B (Bialgebra.counitAlgHom k B b) := rfl
private lemma proj_of_mem (x : ↥(augIdeal k B)) : proj (k := k) (x : B) = x := by
  ext
  rw [coe_proj, mem_augIdeal.mp x.2, map_zero, sub_zero]
private lemma proj_one : proj (k := k) (B := B) 1 = 0 := by
  ext
  simp
private lemma proj_algebraMap (r : k) : proj (k := k) (B := B) (algebraMap k B r) = 0 := by
  ext
  simp
private lemma toCotangent_proj_mul (a b : B) :
    (augIdeal k B).toCotangent (proj (a * b)) =
      Bialgebra.counitAlgHom k B a • (augIdeal k B).toCotangent (proj b) +
        Bialgebra.counitAlgHom k B b • (augIdeal k B).toCotangent (proj a) := by
  rw [← (augIdeal k B).toCotangent.map_smul_of_tower (Bialgebra.counitAlgHom k B a) (proj b),
    ← (augIdeal k B).toCotangent.map_smul_of_tower (Bialgebra.counitAlgHom k B b) (proj a), ← map_add,
    Ideal.toCotangent_eq, pow_two]
  have ha : a - algebraMap k B (Bialgebra.counitAlgHom k B a) ∈ augIdeal k B := (proj (k := k) a).2
  have hb : b - algebraMap k B (Bialgebra.counitAlgHom k B b) ∈ augIdeal k B := (proj (k := k) b).2
  convert Ideal.mul_mem_mul ha hb using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, coe_proj, map_mul, Algebra.smul_def]
  ring
private noncomputable def delta (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) : B →ₗ[k] k :=
  ℓ ∘ₗ ((augIdeal k B).toCotangent.restrictScalars k) ∘ₗ proj
@[simp] lemma delta_apply (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) (b : B) :
    delta ℓ b = ℓ ((augIdeal k B).toCotangent (proj b)) := rfl
private noncomputable def DLin (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) : B →ₗ[k] DualNumber k :=
  (Algebra.linearMap k (DualNumber k)) ∘ₗ (Bialgebra.counitAlgHom k B).toLinearMap +
    (TrivSqZeroExt.inrHom k k) ∘ₗ delta ℓ
@[simp] lemma fst_DLin (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) (b : B) :
    TrivSqZeroExt.fst (DLin ℓ b) = Bialgebra.counitAlgHom k B b := by
  simp [DLin, Algebra.linearMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
@[simp] lemma snd_DLin (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) (b : B) :
    TrivSqZeroExt.snd (DLin ℓ b) = delta ℓ b := by
  simp [DLin, Algebra.linearMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
private noncomputable def DAlg (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) : B →ₐ[k] DualNumber k :=
  AlgHom.ofLinearMap (DLin ℓ)
    (by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_DLin, map_one, TrivSqZeroExt.fst_one]
      · rw [snd_DLin, TrivSqZeroExt.snd_one, delta_apply, proj_one, map_zero, map_zero])
    (by
      intro a b
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [fst_DLin, TrivSqZeroExt.fst_mul, fst_DLin, fst_DLin, map_mul]
      · rw [snd_DLin, DualNumber.snd_mul, fst_DLin, fst_DLin, snd_DLin, snd_DLin, delta_apply,
          toCotangent_proj_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, delta_apply,
          delta_apply, smul_eq_mul, smul_eq_mul]
        ring)
@[simp] lemma DAlg_apply (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) (b : B) : DAlg ℓ b = DLin ℓ b := rfl
private noncomputable def DTan (ℓ : (augIdeal k B).Cotangent →ₗ[k] k) : Tan k B := ⟨DAlg ℓ, fun b => by simp⟩
private noncomputable def gammaEquiv : Tan k B ≃ ((augIdeal k B).Cotangent →ₗ[k] k) where
  toFun := gamma
  invFun := DTan
  left_inv D := by
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    refine TrivSqZeroExt.ext ?_ ?_
    · simp only [DTan, DAlg_apply, fst_DLin]
      exact (D.2 b).symm
    · simp only [DTan, DAlg_apply, snd_DLin, delta_apply, gamma_toCotangent, coe_proj, map_sub,
        TrivSqZeroExt.snd_sub, AlgHom.commutes]
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      simp
  right_inv ℓ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (augIdeal k B).toCotangent_surjective v
    rw [gamma_toCotangent]
    simp only [DTan, DAlg_apply, snd_DLin, delta_apply, proj_of_mem]
private lemma gammaEquiv_apply (D : Tan k B) : gammaEquiv D = gamma D := rfl
/--
[Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom.lean)
-/
@[path]
private lemma main
    (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Bialgebra k B] :
    ∃ γ : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b} ≃
        ((RingHom.ker (Bialgebra.counitAlgHom k B)).Cotangent →ₗ[k] k),
      (∀ (D : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b})
          (x : ↥(RingHom.ker (Bialgebra.counitAlgHom k B))),
          γ D ((RingHom.ker (Bialgebra.counitAlgHom k B)).toCotangent x) =
            TrivSqZeroExt.snd (D.1 (x : B))) ∧
      (∀ (q : B →ₐ[k] B)
          (hq : RingHom.ker (Bialgebra.counitAlgHom k B) ≤
            (RingHom.ker (Bialgebra.counitAlgHom k B)).comap q)
          (D D' : {D : B →ₐ[k] DualNumber k //
            ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b}),
          (∀ b : B, D'.1 b = D.1 (q b)) →
          γ D' = γ D ∘ₗ
            (RingHom.ker (Bialgebra.counitAlgHom k B)).mapCotangent
              (RingHom.ker (Bialgebra.counitAlgHom k B)) q hq) := by
  refine ⟨gammaEquiv, fun D x => gamma_toCotangent D x, ?_⟩
  intro q hq D D' h
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (RingHom.ker (Bialgebra.counitAlgHom k B)).toCotangent_surjective v
  rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, gammaEquiv_apply, gammaEquiv_apply,
    gamma_toCotangent, gamma_toCotangent, h]

-- created on 2026-10-20
