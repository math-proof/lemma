import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


section
variable {k B : Type*} [CommRing k] [CommRing B] [Bialgebra k B]

private abbrev augIdeal : Ideal B := RingHom.ker (Bialgebra.counitAlgHom k B)
private abbrev Tan := Subtype fun D : B →ₐ[k] DualNumber k => ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b
private lemma mem_augIdeal {b : B} : b ∈ augIdeal ↔ Bialgebra.counitAlgHom k B b = 0 := RingHom.mem_ker
private noncomputable def dLin (D : B →ₐ[k] DualNumber k) : B →ₗ[k] k := LinearMap.comp (TrivSqZeroExt.sndHom k k) D.toLinearMap
@[simp] private lemma dLin_apply (D : B →ₐ[k] DualNumber k) (b : B) : dLin D b = TrivSqZeroExt.snd (D b) := rfl
private noncomputable def dI (D : B →ₐ[k] DualNumber k) : augIdeal →ₗ[k] k := LinearMap.comp (dLin D) (augIdeal.subtype.restrictScalars k)
@[simp] private lemma dI_apply (D : B →ₐ[k] DualNumber k) (x : augIdeal) : dI D x = TrivSqZeroExt.snd (D (x : B)) := rfl
private lemma dI_mul (D : Tan) (x y : augIdeal) : dI D.1 (x * y) = 0 := by
  have hx : Bialgebra.counitAlgHom k B (x : B) = 0 := mem_augIdeal.mp x.2
  have hy : Bialgebra.counitAlgHom k B (y : B) = 0 := mem_augIdeal.mp y.2
  rw [dI_apply]
  have : ((x * y : augIdeal) : B) = (x : B) * (y : B) := rfl
  rw [this, map_mul, DualNumber.snd_mul, D.2, D.2, hx, hy, zero_mul, mul_zero, add_zero]
private noncomputable def gamma (D : Tan) : augIdeal.Cotangent →ₗ[k] k := Ideal.Cotangent.lift (dI D.1) (dI_mul D)
@[simp] private lemma gamma_toCotangent (D : Tan) (x : augIdeal) : gamma D (augIdeal.toCotangent x) = TrivSqZeroExt.snd (D.1 (x : B)) := by
  simp [gamma]
private noncomputable def projFun (b : B) : augIdeal := ⟨b - algebraMap k B (Bialgebra.counitAlgHom k B b), by rw [mem_augIdeal, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]⟩
private lemma proj_add (a b : B) : projFun (a + b) = projFun a + projFun b := by
  ext
  simp only [projFun, map_add, Submodule.coe_add]
  ring
private lemma proj_smul (r : k) (b : B) : projFun (r • b) = r • projFun b := by
  ext
  simp only [projFun, RingHom.id_apply, Submodule.coe_smul_of_tower, map_mul, Algebra.smul_def, AlgHom.commutes, Algebra.algebraMap_self_apply]
  ring
private noncomputable def proj : B →ₗ[k] augIdeal := LinearMap.mk (AddHom.mk projFun proj_add) proj_smul
@[simp] private lemma coe_proj (b : B) : (proj b : B) = b - algebraMap k B (Bialgebra.counitAlgHom k B b) := rfl
private lemma proj_of_mem (x : augIdeal) : proj (x : B) = x := by
  ext
  rw [coe_proj, mem_augIdeal.mp x.2, map_zero, sub_zero]
private lemma proj_one : proj (1 : B) = 0 := by
  ext
  simp
private lemma proj_algebraMap (r : k) : proj (algebraMap k B r) = 0 := by
  ext
  simp
private lemma toCotangent_proj_mul (a b : B) : augIdeal.toCotangent (proj (a * b)) = Bialgebra.counitAlgHom k B a • augIdeal.toCotangent (proj b) + Bialgebra.counitAlgHom k B b • augIdeal.toCotangent (proj a) := by
  rw [← augIdeal.toCotangent.map_smul_of_tower (Bialgebra.counitAlgHom k B a) (proj b), ← augIdeal.toCotangent.map_smul_of_tower (Bialgebra.counitAlgHom k B b) (proj a), ← map_add, Ideal.toCotangent_eq, pow_two]
  have ha : a - algebraMap k B (Bialgebra.counitAlgHom k B a) ∈ augIdeal := (proj a).2
  have hb : b - algebraMap k B (Bialgebra.counitAlgHom k B b) ∈ augIdeal := (proj b).2
  convert Ideal.mul_mem_mul ha hb using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, coe_proj, map_mul, Algebra.smul_def]
  ring
private noncomputable def delta (ℓ : augIdeal.Cotangent →ₗ[k] k) : B →ₗ[k] k := LinearMap.comp ℓ (LinearMap.comp (augIdeal.toCotangent.restrictScalars k) proj)
@[simp] private lemma delta_apply (ℓ : augIdeal.Cotangent →ₗ[k] k) (b : B) : delta ℓ b = ℓ (augIdeal.toCotangent (proj b)) := rfl
private noncomputable def DLin (ℓ : augIdeal.Cotangent →ₗ[k] k) : B →ₗ[k] DualNumber k := LinearMap.comp (Algebra.linearMap k (DualNumber k)) (Bialgebra.counitAlgHom k B).toLinearMap + LinearMap.comp (TrivSqZeroExt.inrHom k k) (delta ℓ)
@[simp] private lemma fst_DLin (ℓ : augIdeal.Cotangent →ₗ[k] k) (b : B) : TrivSqZeroExt.fst (DLin ℓ b) = Bialgebra.counitAlgHom k B b := by
  simp [DLin, Algebra.linearMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
@[simp] private lemma snd_DLin (ℓ : augIdeal.Cotangent →ₗ[k] k) (b : B) : TrivSqZeroExt.snd (DLin ℓ b) = delta ℓ b := by
  simp [DLin, Algebra.linearMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
private lemma DAlg_map_one (ℓ : augIdeal.Cotangent →ₗ[k] k) : DLin ℓ 1 = 1 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_DLin, map_one, TrivSqZeroExt.fst_one]
  · rw [snd_DLin, TrivSqZeroExt.snd_one, delta_apply, proj_one, map_zero, map_zero]
private lemma DAlg_map_mul (ℓ : augIdeal.Cotangent →ₗ[k] k) (a b : B) : DLin ℓ (a * b) = DLin ℓ a * DLin ℓ b := by
  refine TrivSqZeroExt.ext ?_ ?_
  ·
    rw [fst_DLin, TrivSqZeroExt.fst_mul, fst_DLin, fst_DLin, map_mul]
  ·
    rw [snd_DLin, DualNumber.snd_mul, fst_DLin, fst_DLin, snd_DLin, snd_DLin, delta_apply, toCotangent_proj_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, delta_apply, delta_apply, smul_eq_mul, smul_eq_mul]
    ring
private noncomputable def DAlg (ℓ : augIdeal.Cotangent →ₗ[k] k) : B →ₐ[k] DualNumber k := AlgHom.ofLinearMap (DLin ℓ) (DAlg_map_one ℓ) (DAlg_map_mul ℓ)
@[simp] private lemma DAlg_apply (ℓ : augIdeal.Cotangent →ₗ[k] k) (b : B) : DAlg ℓ b = DLin ℓ b := rfl
private noncomputable def DTan (ℓ : augIdeal.Cotangent →ₗ[k] k) : Tan := ⟨DAlg ℓ, fun b => by simp⟩
private lemma gammaEquiv_left (D : Tan) : DTan (gamma D) = D := by
  apply Subtype.ext
  apply AlgHom.ext
  intro b
  refine TrivSqZeroExt.ext ?_ ?_
  ·
    simp only [DTan, DAlg_apply, fst_DLin]
    apply (D.2 b).symm
  ·
    simp only [DTan, DAlg_apply, snd_DLin, delta_apply, gamma_toCotangent, coe_proj, map_sub, TrivSqZeroExt.snd_sub, AlgHom.commutes]
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    simp
private lemma gammaEquiv_right (ℓ : augIdeal.Cotangent →ₗ[k] k) : gamma (DTan ℓ) = ℓ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := augIdeal.toCotangent_surjective v
  rw [gamma_toCotangent]
  simp only [DTan, DAlg_apply, snd_DLin, delta_apply, proj_of_mem]
private noncomputable def gammaEquiv : Tan ≃ (augIdeal.Cotangent →ₗ[k] k) := ⟨gamma, DTan, gammaEquiv_left, gammaEquiv_right⟩
private lemma gammaEquiv_apply (D : Tan) : gammaEquiv D = gamma D := rfl

end

/--
[Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_equiv_algHom_dualNumber_over_counit_linearMap_cotangent_ker_counitAlgHom.lean)
-/
@[path]
private lemma main
  [CommRing k] [CommRing B] [Bialgebra k B] :
  -- imply
  ∃ γ : Subtype (fun D : B →ₐ[k] DualNumber k => ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b) ≃ ((RingHom.ker (Bialgebra.counitAlgHom k B)).Cotangent →ₗ[k] k), (∀ (D : Subtype fun D : B →ₐ[k] DualNumber k => ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b) (x : RingHom.ker (Bialgebra.counitAlgHom k B)), γ D ((RingHom.ker (Bialgebra.counitAlgHom k B)).toCotangent x) = TrivSqZeroExt.snd (D.1 (x : B))) ∧ (∀ (q : B →ₐ[k] B) (hq : RingHom.ker (Bialgebra.counitAlgHom k B) ≤ (RingHom.ker (Bialgebra.counitAlgHom k B)).comap q) (D D' : Subtype fun D : B →ₐ[k] DualNumber k => ∀ b : B, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k B b), (∀ b : B, D'.1 b = D.1 (q b)) → γ D' = LinearMap.comp (γ D) ((RingHom.ker (Bialgebra.counitAlgHom k B)).mapCotangent (RingHom.ker (Bialgebra.counitAlgHom k B)) q hq)) := by
  -- proof
  refine ⟨gammaEquiv, fun D x => gamma_toCotangent D x, ?_⟩
  intro q hq D D' h
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (RingHom.ker (Bialgebra.counitAlgHom k B)).toCotangent_surjective v
  rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, gammaEquiv_apply, gammaEquiv_apply, gamma_toCotangent, gamma_toCotangent, h]


-- created on 2026-10-20
