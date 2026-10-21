import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Bialgebra k A]
variable {B : Type w} [CommRing B] [Bialgebra k B]
variable {C : Type x} [CommRing C] [Bialgebra k C]
private abbrev pushIdeal (π : A →ₐc[k] B) (μ : A →ₐc[k] C) : Ideal B :=
  Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] C))
private noncomputable def comulTo (π : A →ₐc[k] B) (μ : A →ₐc[k] C) :
    B →ₐ[k] (B ⧸ pushIdeal π μ) ⊗[k] (B ⧸ pushIdeal π μ) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
    (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp (Bialgebra.comulAlgHom k B)
private noncomputable def throughMu (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    C →ₐ[k] B ⧸ pushIdeal π μ :=
  (Ideal.Quotient.liftₐ (RingHom.ker (μ : A →ₐ[k] C))
      ((Ideal.Quotient.mkₐ k (pushIdeal π μ)).comp (π : A →ₐ[k] B))
      (fun a ha => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (f := (μ : A →ₐ[k] C)) hμ).symm.toAlgHom
private lemma throughMu_comp (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    (throughMu π μ hμ).comp (μ : A →ₐ[k] C) =
      (Ideal.Quotient.mkₐ k (pushIdeal π μ)).comp (π : A →ₐ[k] B) := by
  ext a
  have h : (Ideal.quotientKerAlgEquivOfSurjective (f := (μ : A →ₐ[k] C)) hμ).symm (μ a)
      = Ideal.Quotient.mk (RingHom.ker (μ : A →ₐ[k] C)) a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (μ : A →ₐ[k] C)) hμ a).symm
  simp [throughMu, h]
private lemma comulTo_eq_zero (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ)
    (b : B) (hb : b ∈ pushIdeal π μ) : comulTo π μ b = 0 := by
  have key : (comulTo π μ).comp (π : A →ₐ[k] B) =
      (Algebra.TensorProduct.map (throughMu π μ hμ) (throughMu π μ hμ)).comp
        ((Bialgebra.comulAlgHom k C).comp (μ : A →ₐ[k] C)) := by
    rw [← BialgHom.map_comp_comulAlgHom μ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
      throughMu_comp, Algebra.TensorProduct.map_comp, AlgHom.comp_assoc,
      BialgHom.map_comp_comulAlgHom π]
    rfl
  have hgen : ∀ a : A, a ∈ RingHom.ker (μ : A →ₐ[k] C) → comulTo π μ ((π : A →ₐ[k] B) a) = 0 := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have := AlgHom.congr_fun key a
    simp only [AlgHom.comp_apply] at this
    rw [this, ha, map_zero, map_zero]
  have hI : pushIdeal π μ ≤ RingHom.ker (comulTo π μ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hgen a ha
  exact hI hb
private lemma counit_eq_zero (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (b : B) (hb : b ∈ pushIdeal π μ) :
    Bialgebra.counitAlgHom k B b = 0 := by
  have hI : pushIdeal π μ ≤ RingHom.ker (Bialgebra.counitAlgHom k B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [RingHom.mem_ker] at ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 := AlgHom.congr_fun (BialgHom.counitAlgHom_comp π) a
    have h2 := AlgHom.congr_fun (BialgHom.counitAlgHom_comp μ) a
    simp only [AlgHom.comp_apply] at h1 h2
    rw [h1, ← h2, ha, map_zero]
  exact hI hb
private noncomputable def comulQ (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    B ⧸ pushIdeal π μ →ₐ[k] (B ⧸ pushIdeal π μ) ⊗[k] (B ⧸ pushIdeal π μ) :=
  Ideal.Quotient.liftₐ (pushIdeal π μ) (comulTo π μ) (comulTo_eq_zero π μ hμ)
private noncomputable def counitQ (π : A →ₐc[k] B) (μ : A →ₐc[k] C) : B ⧸ pushIdeal π μ →ₐ[k] k :=
  Ideal.Quotient.liftₐ (pushIdeal π μ) (Bialgebra.counitAlgHom k B) (counit_eq_zero π μ)
private lemma comulQ_comp_mk (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    (comulQ π μ hμ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) = comulTo π μ :=
  Ideal.Quotient.liftₐ_comp _ _ _
private lemma counitQ_comp_mk (π : A →ₐc[k] B) (μ : A →ₐc[k] C) :
    (counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) = Bialgebra.counitAlgHom k B :=
  Ideal.Quotient.liftₐ_comp _ _ _
private lemma coassoc_algHom :
    (Algebra.TensorProduct.assoc k k k B B B).toAlgHom.comp
        ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k B)).comp
          (Bialgebra.comulAlgHom k B)) =
      (Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.comulAlgHom k B)).comp
        (Bialgebra.comulAlgHom k B) := by
  apply AlgHom.toLinearMap_injective
  ext b
  exact Coalgebra.coassoc_apply (R := k) b
private lemma rTensor_algHom :
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k B) (AlgHom.id k B)).comp
        (Bialgebra.comulAlgHom k B) = (Algebra.TensorProduct.lid k B).symm.toAlgHom := by
  apply AlgHom.toLinearMap_injective
  ext b
  exact Coalgebra.rTensor_counit_comul (R := k) b
private lemma lTensor_algHom :
    (Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.counitAlgHom k B)).comp
        (Bialgebra.comulAlgHom k B) = (Algebra.TensorProduct.rid k k B).symm.toAlgHom := by
  apply AlgHom.toLinearMap_injective
  ext b
  exact Coalgebra.lTensor_counit_comul (R := k) b
private lemma assoc_naturality {Q : Type w} [CommRing Q] [Algebra k Q] (f : B →ₐ[k] Q) :
    (Algebra.TensorProduct.assoc k k k Q Q Q).toAlgHom.comp
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f) =
      (Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)).comp
        (Algebra.TensorProduct.assoc k k k B B B).toAlgHom := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext_threefold
  intro x y z
  simp
private lemma lid_naturality {Q : Type w} [CommRing Q] [Algebra k Q] (f : B →ₐ[k] Q) :
    (Algebra.TensorProduct.map (AlgHom.id k k) f).comp (Algebra.TensorProduct.lid k B).symm.toAlgHom =
      (Algebra.TensorProduct.lid k Q).symm.toAlgHom.comp f := by
  ext b
  simp
private lemma rid_naturality {Q : Type w} [CommRing Q] [Algebra k Q] (f : B →ₐ[k] Q) :
    (Algebra.TensorProduct.map f (AlgHom.id k k)).comp (Algebra.TensorProduct.rid k k B).symm.toAlgHom =
      (Algebra.TensorProduct.rid k k Q).symm.toAlgHom.comp f := by
  ext b
  simp
@[reducible]
private noncomputable def quotBialgebra (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    Bialgebra k (B ⧸ pushIdeal π μ) := by
  have hmk : (comulQ π μ hμ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp (Bialgebra.comulAlgHom k B) := comulQ_comp_mk π μ hμ
  have hε : (counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) = Bialgebra.counitAlgHom k B :=
    counitQ_comp_mk π μ
  refine Bialgebra.ofAlgHom (comulQ π μ hμ) (counitQ π μ) ?_ ?_ ?_
  · apply Ideal.Quotient.algHom_ext
    calc ((Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
            ((Algebra.TensorProduct.map (comulQ π μ hμ) (AlgHom.id k _)).comp (comulQ π μ hμ))).comp
          (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        = (Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
            ((Algebra.TensorProduct.map ((comulQ π μ hμ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
              ((AlgHom.id k _).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp
                (Bialgebra.comulAlgHom k B)) := by
          rw [Algebra.TensorProduct.map_comp, AlgHom.comp_assoc, AlgHom.comp_assoc, AlgHom.comp_assoc, hmk]
      _ = (Algebra.TensorProduct.assoc k k k _ _ _).toAlgHom.comp
            ((Algebra.TensorProduct.map
                (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
                  (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
                (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp
              ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k B)).comp
                (Bialgebra.comulAlgHom k B))) := by
          rw [hmk, AlgHom.id_comp, ← AlgHom.comp_id (Ideal.Quotient.mkₐ k (pushIdeal π μ)),
            Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.comp_assoc]
      _ = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
              (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
                (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp
            ((Algebra.TensorProduct.assoc k k k B B B).toAlgHom.comp
              ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k B)).comp
                (Bialgebra.comulAlgHom k B))) := by
          rw [← AlgHom.comp_assoc, assoc_naturality, AlgHom.comp_assoc]
      _ = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
              (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
                (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp
            ((Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.comulAlgHom k B)).comp
              (Bialgebra.comulAlgHom k B)) := by rw [coassoc_algHom]
      _ = (Algebra.TensorProduct.map (AlgHom.id k _) (comulQ π μ hμ)).comp
            ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ))
              (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp (Bialgebra.comulAlgHom k B)) := by
          rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
            ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp, hmk]
      _ = ((Algebra.TensorProduct.map (AlgHom.id k _) (comulQ π μ hμ)).comp (comulQ π μ hμ)).comp
            (Ideal.Quotient.mkₐ k (pushIdeal π μ)) := by rw [AlgHom.comp_assoc, hmk]
  · apply Ideal.Quotient.algHom_ext
    calc ((Algebra.TensorProduct.map (counitQ π μ) (AlgHom.id k _)).comp (comulQ π μ hμ)).comp
          (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        = (Algebra.TensorProduct.map ((counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
            ((AlgHom.id k _).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp (Bialgebra.comulAlgHom k B) := by
          rw [AlgHom.comp_assoc, hmk, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
      _ = (Algebra.TensorProduct.map (AlgHom.id k k) (Ideal.Quotient.mkₐ k (pushIdeal π μ))).comp
            ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom k B) (AlgHom.id k B)).comp
              (Bialgebra.comulAlgHom k B)) := by
          rw [hε, AlgHom.id_comp, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
            AlgHom.comp_id]
      _ = (Algebra.TensorProduct.lid k _).symm.toAlgHom.comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) := by
          rw [rTensor_algHom, lid_naturality]
  · apply Ideal.Quotient.algHom_ext
    calc ((Algebra.TensorProduct.map (AlgHom.id k _) (counitQ π μ)).comp (comulQ π μ hμ)).comp
          (Ideal.Quotient.mkₐ k (pushIdeal π μ))
        = (Algebra.TensorProduct.map ((AlgHom.id k _).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))
            ((counitQ π μ).comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)))).comp (Bialgebra.comulAlgHom k B) := by
          rw [AlgHom.comp_assoc, hmk, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp]
      _ = (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (pushIdeal π μ)) (AlgHom.id k k)).comp
            ((Algebra.TensorProduct.map (AlgHom.id k B) (Bialgebra.counitAlgHom k B)).comp
              (Bialgebra.comulAlgHom k B)) := by
          rw [hε, AlgHom.id_comp, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp,
            AlgHom.comp_id]
      _ = (Algebra.TensorProduct.rid k k _).symm.toAlgHom.comp (Ideal.Quotient.mkₐ k (pushIdeal π μ)) := by
          rw [lTensor_algHom, rid_naturality]
private noncomputable def mkBialgHom (π : A →ₐc[k] B) (μ : A →ₐc[k] C) (hμ : Function.Surjective μ) :
    let _ := quotBialgebra π μ hμ
    B →ₐc[k] B ⧸ pushIdeal π μ :=
  let _ := quotBialgebra π μ hμ
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ k (pushIdeal π μ)) (counitQ_comp_mk π μ) (comulQ_comp_mk π μ hμ)
/--
[Bialgebra_exists_surjective_bialgHom_ker_eq_map_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_surjective_bialgHom_ker_eq_map_ker.lean)
-/
@[path]
private lemma main
    (k : Type u) [Field k]
    {A : Type v} [CommRing A] [Bialgebra k A]
    {B : Type w} [CommRing B] [Bialgebra k B]
    {C : Type x} [CommRing C] [Bialgebra k C]
    (π : A →ₐc[k] B) (μ : A →ₐc[k] C)
    (hπ : Function.Surjective π) (hμ : Function.Surjective μ) :
    ∃ (D : Type w) (_ : CommRing D) (_ : Bialgebra k D) (ρ : B →ₐc[k] D),
      Function.Surjective ρ ∧
      RingHom.ker (ρ : B →ₐ[k] D) = Ideal.map (π : A →ₐ[k] B) (RingHom.ker (μ : A →ₐ[k] C)) := by
  have _ := hπ
  let _ : Bialgebra k (B ⧸ pushIdeal π μ) := quotBialgebra π μ hμ
  refine ⟨B ⧸ pushIdeal π μ, inferInstance, inferInstance, mkBialgHom π μ hμ, ?_, ?_⟩
  · exact Ideal.Quotient.mk_surjective
  · exact Ideal.mk_ker

-- created on 2026-10-20
