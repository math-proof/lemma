import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def DescentCondition
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (I : Ideal B) : Prop :=
  I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
    I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)

private lemma map_comap_eq_self_of_descentCondition_of_section
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (σ : B →ₐ[A] A)
  (I : Ideal B)
  -- given
  (hI : DescentCondition (A := A) I) :
  -- imply
  (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  -- proof
  refine le_antisymm Ideal.map_comap_le ?_
  let θ : B ⊗[A] B →ₐ[A] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId A B).comp σ) (AlgHom.id A B) fun _ _ => Commute.all _ _
  have hθL : (θ : B ⊗[A] B →+* B).comp
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      (algebraMap A B).comp (σ : B →+* A) := by
    ext b
    simp [θ, Algebra.TensorProduct.includeLeftRingHom]
  have hθR : (θ : B ⊗[A] B →+* B).comp
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) = RingHom.id B := by
    ext b
    simp [θ]
  have h2 : I.map (σ : B →+* A) ≤ I.comap (algebraMap A B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    change algebraMap A B (σ i) ∈ I
    have hmem : Algebra.TensorProduct.includeLeftRingHom i ∈
      I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) := by
      rw [← show I.map _ = _ from hI]
      apply Ideal.mem_map_of_mem _ hi
    have := Ideal.mem_map_of_mem (θ : B ⊗[A] B →+* B) hmem
    rw [Ideal.map_map, hθR, Ideal.map_id] at this
    convert this using 1
    apply (RingHom.congr_fun hθL i).symm
  suffices h1 : I ≤ (I.map (σ : B →+* A)).map (algebraMap A B) by
    apply h1.trans (Ideal.map_mono h2)
  intro i hi
  have hmem : ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) i ∈
    I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) := by
    rw [show I.map _ = _ from hI]
    apply Ideal.mem_map_of_mem _ hi
  have := Ideal.mem_map_of_mem (θ : B ⊗[A] B →+* B) hmem
  rw [Ideal.map_map, hθL, ← Ideal.map_map] at this
  convert this using 1
  apply (RingHom.congr_fun hθR i).symm

private lemma descentCondition_map
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (I₀ : Ideal A) :
  -- imply
  DescentCondition (A := A) (I₀.map (algebraMap A B)) := by
  -- proof
  unfold DescentCondition
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_one_eq_one_tmul]

private lemma comap_includeLeft_map_includeRight
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
  (I : Ideal B) :
  -- imply
  (I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)).comap
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
    (I.comap (algebraMap A B)).map (algebraMap A B) := by
  -- proof
  set I₀ := I.comap (algebraMap A B) with hI₀
  refine le_antisymm ?_ ?_
  ·
    intro b hb
    rw [Ideal.mem_comap] at hb
    let g : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⧸ I) :=
      Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A I)
    have hker : I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) ≤
        RingHom.ker (g : B ⊗[A] B →+* B ⊗[A] (B ⧸ I)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change g ((1 : B) ⊗ₜ[A] i) = 0
      have hg : g ((1 : B) ⊗ₜ[A] i) = (AlgHom.id A B 1) ⊗ₜ[A] (Ideal.Quotient.mkₐ A I i) :=
        Algebra.TensorProduct.map_tmul _ _ _ _
      rw [hg, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hi, TensorProduct.tmul_zero]
    have hb0 : b ⊗ₜ[A] (1 : B ⧸ I) = 0 := by
      have := hker hb
      simpa [g, Algebra.TensorProduct.includeLeftRingHom] using this
    have hH : I₀ ≤ I.comap (Algebra.ofId A B : A →+* B) := le_of_eq hI₀
    let ι : (A ⧸ I₀) →ₐ[A] (B ⧸ I) := Ideal.quotientMapₐ I (Algebra.ofId A B) hH
    have hι : Function.Injective ι.toLinearMap :=
      Ideal.quotientMap_injective' (I := I) (f := (Algebra.ofId A B : A →+* B)) (H := hH)
        (le_of_eq hI₀.symm)
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B) ι.toLinearMap hι
    have h1 : (LinearMap.lTensor B ι.toLinearMap) (b ⊗ₜ[A] (1 : A ⧸ I₀)) = 0 := by
      rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one, hb0]
    have h2 : b ⊗ₜ[A] (1 : A ⧸ I₀) = 0 := hinj (by rw [h1, map_zero])
    apply Iff.mp Ideal.Quotient.eq_zero_iff_mem
    apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).injective
    rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, h2]
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap] at ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : Algebra.TensorProduct.includeLeftRingHom (algebraMap A B a) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (algebraMap A B a) := by
      simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.algebraMap_eq_smul_one]
    rw [this]
    apply Ideal.mem_map_of_mem _ ha

private lemma map_comap_eq_self_of_descentCondition
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
  (I : Ideal B)
  -- given
  (hI : DescentCondition (A := A) I) :
  -- imply
  (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  -- proof
  set iL : B →+* B ⊗[A] B := Algebra.TensorProduct.includeLeftRingHom
  set iR : B →+* B ⊗[A] B :=
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)
  have hI' : I.map iL = I.map iR := hI
  let jL : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B) := Algebra.TensorProduct.includeLeftRingHom
  let jR : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)) : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B))
  let χ₁ : B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeLeft : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let χ₂ : B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let χ : B ⊗[A] B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    Algebra.TensorProduct.lift χ₁ χ₂ fun x y => Commute.all (χ₁ x) (χ₂ y)
  have hχL : (χ : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).comp iL = jL.comp iR := by
    ext b
    simp [χ, χ₁, χ₂, iL, iR, jL, Algebra.TensorProduct.includeLeftRingHom]
    rfl
  have hχR : (χ : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).comp iR = jR.comp iR := by
    ext b
    simp [χ, χ₁, χ₂, iR, jR]
    rfl
  have hDC : DescentCondition (A := B) (I.map iR) := by
    change (I.map iR).map jL = (I.map iR).map jR
    rw [Ideal.map_map, Ideal.map_map, ← hχL, ← hχR, ← Ideal.map_map, ← Ideal.map_map, hI']
  have hsplit := map_comap_eq_self_of_descentCondition_of_section
    (Algebra.TensorProduct.lmul'' A (S := B)) (I.map iR) hDC
  have halg : algebraMap B (B ⊗[A] B) = iL := rfl
  rw [halg, comap_includeLeft_map_includeRight] at hsplit
  rw [← hI'] at hsplit
  have := congrArg (fun J => J.comap iL) hsplit
  rwa [← halg, Ideal.comap_map_eq_self_of_faithfullyFlat,
    Ideal.comap_map_eq_self_of_faithfullyFlat] at this

/--
[Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight.lean)
-/
@[path]
private lemma main
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
  (I : Ideal B)
  -- given
  (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
    I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)) :
  -- imply
  (I.comap (algebraMap A B)).map (algebraMap A B) = I :=
  map_comap_eq_self_of_descentCondition I hI


-- created on 2026-10-20
