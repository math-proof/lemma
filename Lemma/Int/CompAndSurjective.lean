import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {H₁ : Type v} [CommRing H₁] [Bialgebra R H₁]
  {H₂ : Type v} [CommRing H₂] [Bialgebra R H₂]
  {H₁' : Type v} [CommRing H₁'] [Bialgebra R H₁']
  {H₂' : Type v} [CommRing H₂'] [Bialgebra R H₂']
  (π₁ : BialgHom R H₁ H₁')
  (π₂ : BialgHom R H₂ H₂')
  (r : BialgHom R H₂ H₁)
  -- given
  (hπ₂ : Function.Surjective π₂)
  (hker : ∀ x : H₂, π₂ x = 0 → π₁ (r x) = 0) :
  -- imply
  ∃ r' : BialgHom R H₂' H₁', r'.comp π₂ = π₁.comp r ∧ (Function.Surjective π₁ → Function.Surjective r → Function.Surjective r') := by
  -- proof
  classical
  have hker' : RingHom.ker (π₂ : RingHom H₂ H₂') ≤ RingHom.ker ((π₁ : RingHom H₁ H₁').comp (r : RingHom H₂ H₁)) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    apply hker x hx
  let f : RingHom H₂' H₁' := RingHom.liftOfSurjective (π₂ : RingHom H₂ H₂') hπ₂ ⟨(π₁ : RingHom H₁ H₁').comp (r : RingHom H₂ H₁), hker'⟩
  have hf : ∀ x : H₂, f (π₂ x) = π₁ (r x) := by
    intro x
    apply RingHom.liftOfRightInverse_comp_apply (π₂ : RingHom H₂ H₂') _ _ _ x
  let fa : AlgHom R H₂' H₁' :=
    { f with
      commutes' := fun c => by
        have h := hf (algebraMap R H₂ c)
        rw [AlgHomClass.commutes π₂, AlgHomClass.commutes r, AlgHomClass.commutes π₁] at h
        apply h }
  have hfa : ∀ x : H₂, fa (π₂ x) = π₁ (r x) := hf
  have hcounit : (Bialgebra.counitAlgHom R H₁').comp fa = Bialgebra.counitAlgHom R H₂' := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    change Coalgebra.counit (fa (π₂ x)) = Coalgebra.counit (π₂ x)
    rw [hfa, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  have hcomul : (Algebra.TensorProduct.map fa fa).comp (Bialgebra.comulAlgHom R H₂') = (Bialgebra.comulAlgHom R H₁').comp fa := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    change Algebra.TensorProduct.map fa fa (Coalgebra.comul (π₂ x)) = Coalgebra.comul (fa (π₂ x))
    rw [hfa, ← CoalgHomClass.map_comp_comul_apply, ← CoalgHomClass.map_comp_comul_apply, ← CoalgHomClass.map_comp_comul_apply]
    have key : LinearMap.comp (Algebra.TensorProduct.map fa fa).toLinearMap (TensorProduct.map (π₂ : H₂ →ₗ[R] H₂') (π₂ : H₂ →ₗ[R] H₂')) = LinearMap.comp (TensorProduct.map (π₁ : H₁ →ₗ[R] H₁') (π₁ : H₁ →ₗ[R] H₁')) (TensorProduct.map (r : H₂ →ₗ[R] H₁) (r : H₂ →ₗ[R] H₁)) := by
      apply TensorProduct.ext'
      intro a b
      simp [hfa]
    refine congrArg (fun g => g (Coalgebra.comul (R := R) x)) key
  refine ⟨BialgHom.ofAlgHom fa hcounit hcomul, ?_, ?_⟩
  ·
    apply BialgHom.coe_toAlgHom_injective
    apply AlgHom.ext
    intro x
    apply hfa x
  ·
    intro hπ₁ hr z
    obtain ⟨y, rfl⟩ := hπ₁ z
    obtain ⟨x, rfl⟩ := hr y
    refine ⟨π₂ x, hfa x⟩


-- created on 2026-10-20
