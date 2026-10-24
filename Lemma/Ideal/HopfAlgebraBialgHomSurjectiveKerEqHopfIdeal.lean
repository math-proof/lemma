import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

section
variable {F : Type u} [Field F] {A : Type v} [CommRing A] [HopfAlgebra F A]
variable (I : Ideal A)
variable (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I) (Coalgebra.comul (R := F) a) = 0)
variable (hcounit : ∀ a ∈ I, Coalgebra.counit (R := F) a = 0)
variable (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := F) a ∈ I)
private noncomputable def comulQ : (A ⧸ I) →ₐ[F] (A ⧸ I) ⊗[F] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)).comp
      (Bialgebra.comulAlgHom F A))
    (fun a ha => by simpa [Bialgebra.comulAlgHom_apply] using hcomul a ha)
private lemma comulQ_mk
  (a : A) :
    comulQ I hcomul (Ideal.Quotient.mk I a) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)
        (Coalgebra.comul (R := F) a) := rfl
private lemma comulQ_comp_mk :
  (comulQ I hcomul).comp (Ideal.Quotient.mkₐ F I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)).comp
        (Bialgebra.comulAlgHom F A) := by
  ext a; rfl
private noncomputable def counitQ : (A ⧸ I) →ₐ[F] F :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom F A) (fun a ha => by simpa using hcounit a ha)
private lemma counitQ_mk
  (a : A) : counitQ I hcounit (Ideal.Quotient.mk I a) = Coalgebra.counit (R := F) a := rfl
private lemma counitQ_comp_mk : (counitQ I hcounit).comp (Ideal.Quotient.mkₐ F I) = Bialgebra.counitAlgHom F A := by
  ext a; rfl
private noncomputable def antipodeAlgHom : A →ₐ[F] A :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode (R := F))
    (HopfAlgebra.antipode_one (R := F) (A := A))
    (fun a b => by rw [HopfAlgebra.antipode_mul_distrib])
private lemma antipodeAlgHom_apply
  (a : A) : antipodeAlgHom (F := F) a = HopfAlgebraStruct.antipode (R := F) a := rfl
private noncomputable def antipodeQ : (A ⧸ I) →ₐ[F] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ F I).comp (antipodeAlgHom (F := F)))
    (fun a ha => by
      simpa [antipodeAlgHom_apply] using Iff.mpr Ideal.Quotient.eq_zero_iff_mem (hanti a ha))
private lemma antipodeQ_mk
  (a : A) :
    antipodeQ I hanti (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (HopfAlgebraStruct.antipode (R := F) a) := rfl
private lemma algMap_apply
  {B C B' C' : Type*} [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    [Algebra F B] [Algebra F C] [Algebra F B'] [Algebra F C'] (f : B →ₐ[F] B') (g : C →ₐ[F] C')
    (z : B ⊗[F] C) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := by
  let _ := hcomul
  let _ := hcounit
  let _ := hanti
  rfl
private lemma law_rTensor :
  (Algebra.TensorProduct.map (counitQ I hcounit) (AlgHom.id F (A ⧸ I))).comp (comulQ I hcomul) =
      ↑(Algebra.TensorProduct.lid F (A ⧸ I)).symm := by
  apply Ideal.Quotient.algHom_ext
  ext a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, comulQ_mk]
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, counitQ_comp_mk, AlgHom.id_comp,
    algMap_apply]
  have h1 : TensorProduct.map (Bialgebra.counitAlgHom F A).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap =
    LinearMap.comp (TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ F I).toLinearMap) ((Coalgebra.counit (R := F) (A := A)).rTensor A) := by
    rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]; rfl
  rw [h1, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
  simp
private lemma law_lTensor :
  (Algebra.TensorProduct.map (AlgHom.id F (A ⧸ I)) (counitQ I hcounit)).comp (comulQ I hcomul) =
      ↑(Algebra.TensorProduct.rid F F (A ⧸ I)).symm := by
  apply Ideal.Quotient.algHom_ext
  ext a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, comulQ_mk]
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, counitQ_comp_mk, AlgHom.id_comp,
    algMap_apply]
  have h1 : TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Bialgebra.counitAlgHom F A).toLinearMap =
    LinearMap.comp (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap LinearMap.id) ((Coalgebra.counit (R := F) (A := A)).lTensor A) := by
    rw [LinearMap.lTensor, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]; rfl
  rw [h1, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul, TensorProduct.map_tmul]
  simp
private lemma law_coassoc :
  ((Algebra.TensorProduct.assoc F F F (A ⧸ I) (A ⧸ I) (A ⧸ I) :
        ((A ⧸ I) ⊗[F] (A ⧸ I)) ⊗[F] (A ⧸ I) ≃ₐ[F] (A ⧸ I) ⊗[F] ((A ⧸ I) ⊗[F] (A ⧸ I))) :
        ((A ⧸ I) ⊗[F] (A ⧸ I)) ⊗[F] (A ⧸ I) →ₐ[F] (A ⧸ I) ⊗[F] ((A ⧸ I) ⊗[F] (A ⧸ I))).comp
        ((Algebra.TensorProduct.map (comulQ I hcomul) (AlgHom.id F (A ⧸ I))).comp (comulQ I hcomul)) =
      (Algebra.TensorProduct.map (AlgHom.id F (A ⧸ I)) (comulQ I hcomul)).comp (comulQ I hcomul) := by
  apply Ideal.Quotient.algHom_ext
  ext a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, comulQ_mk]
  rw [← AlgHom.comp_apply (Algebra.TensorProduct.map (comulQ I hcomul) _), ← Algebra.TensorProduct.map_comp,
    ← AlgHom.comp_apply (Algebra.TensorProduct.map (AlgHom.id F (A ⧸ I)) _), ← Algebra.TensorProduct.map_comp,
    comulQ_comp_mk, AlgHom.id_comp]
  have hL : Algebra.TensorProduct.map
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)).comp
          (Bialgebra.comulAlgHom F A)) (Ideal.Quotient.mkₐ F I) =
      (Algebra.TensorProduct.map (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I))
          (Ideal.Quotient.mkₐ F I)).comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom F A) (AlgHom.id F A)) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  have hR : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I)
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)).comp
          (Bialgebra.comulAlgHom F A)) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I)
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I))).comp
        (Algebra.TensorProduct.map (AlgHom.id F A) (Bialgebra.comulAlgHom F A)) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  rw [hL, hR, AlgHom.comp_apply, AlgHom.comp_apply]
  have hco := Coalgebra.coassoc_apply (R := F) a
  have e1 : Algebra.TensorProduct.map (Bialgebra.comulAlgHom F A) (AlgHom.id F A) (Coalgebra.comul (R := F) a) =
    (Coalgebra.comul (R := F)).rTensor A (Coalgebra.comul (R := F) a) := by
    rw [algMap_apply]; rfl
  have e2 : Algebra.TensorProduct.map (AlgHom.id F A) (Bialgebra.comulAlgHom F A) (Coalgebra.comul (R := F) a) =
    (Coalgebra.comul (R := F)).lTensor A (Coalgebra.comul (R := F) a) := by
    rw [algMap_apply]; rfl
  rw [e1, e2, ← hco]
  set w := (Coalgebra.comul (R := F)).rTensor A (Coalgebra.comul (R := F) a)
  refine TensorProduct.inductionOn w ?_ ?_
  ·
    intro x c
    refine TensorProduct.inductionOn x ?_ ?_
    ·
      intro a1 a2
      simp [Algebra.TensorProduct.assoc_tmul]
    ·
      intro x y hx hy
      simp_all [TensorProduct.add_tmul]
  ·
    intro x y hx hy
    simp_all
@[reducible] private noncomputable def bialgebraQ : Bialgebra F (A ⧸ I) :=
  Bialgebra.ofAlgHom (comulQ I hcomul) (counitQ I hcounit)
    (law_coassoc I hcomul) (law_rTensor I hcomul hcounit) (law_lTensor I hcomul hcounit)
private lemma antipodeQ_comp_mk_linear :
  LinearMap.comp (antipodeQ I hanti).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap =
      LinearMap.comp (Ideal.Quotient.mkₐ F I).toLinearMap (HopfAlgebraStruct.antipode (R := F)) := by
  ext a; rfl
private lemma mul'_comp_map_mk :
  LinearMap.comp (LinearMap.mul' F (A ⧸ I)) (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap) =
      LinearMap.comp (Ideal.Quotient.mkₐ F I).toLinearMap (LinearMap.mul' F A) := by
  let _ := hcomul
  let _ := hcounit
  let _ := hanti
  apply TensorProduct.ext'
  intro a b
  simp [LinearMap.mul'_apply]
@[reducible] private noncomputable def hopfAlgebraQ : HopfAlgebra F (A ⧸ I) :=
  let _ : Bialgebra F (A ⧸ I) := bialgebraQ I hcomul hcounit
  { antipode := (antipodeQ I hanti).toLinearMap
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change (LinearMap.comp (LinearMap.mul' F (A ⧸ I)) (LinearMap.comp ((antipodeQ I hanti).toLinearMap.rTensor (A ⧸ I)) ((comulQ I hcomul).toLinearMap))) (Ideal.Quotient.mk I a) =
        (LinearMap.comp (Algebra.linearMap F (A ⧸ I)) ((counitQ I hcounit).toLinearMap)) (Ideal.Quotient.mk I a)
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulQ_mk, counitQ_mk, algMap_apply]
      have h1 : (antipodeQ I hanti).toLinearMap.rTensor (A ⧸ I)
          (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap
            (Coalgebra.comul (R := F) a)) =
          TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap
            ((HopfAlgebraStruct.antipode (R := F)).rTensor A (Coalgebra.comul (R := F) a)) := by
        have hmaps : LinearMap.comp ((antipodeQ I hanti).toLinearMap.rTensor (A ⧸ I)) (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap) =
            LinearMap.comp (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap) ((HopfAlgebraStruct.antipode (R := F)).rTensor A) := by
          simp only [LinearMap.rTensor, ← TensorProduct.map_comp, antipodeQ_comp_mk_linear,
            LinearMap.id_comp, LinearMap.comp_id]
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hmaps (Coalgebra.comul (R := F) a)
      rw [h1, ← LinearMap.comp_apply, mul'_comp_map_mk, LinearMap.comp_apply,
        HopfAlgebra.mul_antipode_rTensor_comul_apply]
      simp [Algebra.linearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.algebraMap_eq_smul_one]
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change (LinearMap.comp (LinearMap.mul' F (A ⧸ I)) (LinearMap.comp ((antipodeQ I hanti).toLinearMap.lTensor (A ⧸ I)) ((comulQ I hcomul).toLinearMap))) (Ideal.Quotient.mk I a) =
        (LinearMap.comp (Algebra.linearMap F (A ⧸ I)) ((counitQ I hcounit).toLinearMap)) (Ideal.Quotient.mk I a)
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulQ_mk, counitQ_mk, algMap_apply]
      have h1 : (antipodeQ I hanti).toLinearMap.lTensor (A ⧸ I)
          (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap
            (Coalgebra.comul (R := F) a)) =
          TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap
            ((HopfAlgebraStruct.antipode (R := F)).lTensor A (Coalgebra.comul (R := F) a)) := by
        have hmaps : LinearMap.comp ((antipodeQ I hanti).toLinearMap.lTensor (A ⧸ I)) (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap) =
            LinearMap.comp (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap) ((HopfAlgebraStruct.antipode (R := F)).lTensor A) := by
          simp only [LinearMap.lTensor, ← TensorProduct.map_comp, antipodeQ_comp_mk_linear,
            LinearMap.id_comp, LinearMap.comp_id]
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hmaps (Coalgebra.comul (R := F) a)
      rw [h1, ← LinearMap.comp_apply, mul'_comp_map_mk, LinearMap.comp_apply,
        HopfAlgebra.mul_antipode_lTensor_comul_apply]
      simp [Algebra.linearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.algebraMap_eq_smul_one] }
end

/--
[HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.lean)
-/
@[path]
private lemma main
  {F : Type u} [Field F] {A : Type v} [CommRing A] [HopfAlgebra F A] (I : Ideal A)
    (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)
      (Coalgebra.comul (R := F) a) = 0)
    (hcounit : ∀ a ∈ I, Coalgebra.counit (R := F) a = 0)
    (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := F) a ∈ I) :
    -- imply
    ∃ (A' : Type v) (_ : CommRing A') (_ : HopfAlgebra F A') (π : BialgHom F A A'), Function.Surjective π ∧
      RingHom.ker (π : A →+* A') = I ∧
      (Coalgebra.IsCocomm F A → Coalgebra.IsCocomm F A') ∧
      (Module.Finite F A → Module.Finite F A') ∧
      (∀ (T : Type v) [CommRing T] [Algebra F T] (φ : A →ₐ[F] T),
        I ≤ RingHom.ker (φ : A →+* T) → ∃! φ' : A' →ₐ[F] T, φ'.comp (π : A →ₐ[F] A') = φ) := by
  -- proof
  let hH : HopfAlgebra F (A ⧸ I) := hopfAlgebraQ I hcomul hcounit hanti
  let π : BialgHom F A (A ⧸ I) :=
    BialgHom.ofAlgHom (Ideal.Quotient.mkₐ F I) (counitQ_comp_mk I hcounit) (comulQ_comp_mk I hcomul).symm
  have hπ : ∀ a : A, π a = Ideal.Quotient.mk I a := fun a => rfl
  have hπalg : (π : A →ₐ[F] (A ⧸ I)) = Ideal.Quotient.mkₐ F I := by ext a; rfl
  refine ⟨A ⧸ I, inferInstance, hH, π, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, hπ a⟩
  ·
    ext a
    rw [RingHom.mem_ker]
    show π a = 0 ↔ a ∈ I
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem]
  ·
    intro hco
    refine ⟨?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change TensorProduct.comm F (A ⧸ I) (A ⧸ I) (comulQ I hcomul (Ideal.Quotient.mk I a)) =
      comulQ I hcomul (Ideal.Quotient.mk I a)
    rw [comulQ_mk, algMap_apply]
    have hnat : ∀ w : A ⊗[F] A,
        TensorProduct.comm F (A ⧸ I) (A ⧸ I)
          (TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap w) =
        TensorProduct.map (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ F I).toLinearMap
          (TensorProduct.comm F A A w) := by
      intro w
      refine TensorProduct.inductionOn w ?_ ?_
      ·
        intro x y
        simp
      ·
        intro x y hx hy
        simp only [map_add, hx, hy]
    rw [hnat, Coalgebra.comm_comul]
  ·
    intro hfin
    apply Module.Finite.of_surjective (Ideal.Quotient.mkₐ F I).toLinearMap (Ideal.Quotient.mkₐ_surjective F I)
  ·
    intro T _ _ φ hφ
    refine ⟨Ideal.Quotient.liftₐ I φ (fun a ha => hφ ha), ?_, ?_⟩
    ·
      rw [hπalg]
      ext a
      rfl
    ·
      intro ψ hψ
      apply Ideal.Quotient.algHom_ext
      rw [← hπalg, hψ]
      ext a
      rfl


-- created on 2026-10-20
