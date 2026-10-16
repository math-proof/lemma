import Mathlib
import sympy.Basic
open IsLocalRing
open scoped TensorProduct


/--
[Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {A₀ : Type} [CommRing A₀] [IsLocalRing A₀]
  {A : Type} [CommRing A] [IsLocalRing A] [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] [IsAlgClosed (ResidueField A)]
  {B₀ : Type} [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀]
  {𝔪₀ : Ideal B₀} [𝔪₀.IsMaximal]
  {P : Ideal (A ⊗[A₀] B₀)} [P.IsPrime]
-- given
  (h𝔪₀ : ∀ a ∈ maximalIdeal A₀, algebraMap A₀ B₀ a ∈ 𝔪₀)
  (hP₀ : ∀ b ∈ 𝔪₀, (1 : A) ⊗ₜ[A₀] b ∈ P)
  (hPA : ∀ a ∈ maximalIdeal A, a ⊗ₜ[A₀] (1 : B₀) ∈ P) :
-- imply
  ∃ (χ : B₀ →+* ResidueField A) (hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a)),
    let ev : A ⊗[A₀] B₀ →+* ResidueField A :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
        ({ toRingHom := χ
           commutes' := by
             intro a
             rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]
             apply hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
        (fun _ _ => Commute.all _ _)).toRingHom
    P = RingHom.ker ev := by
-- proof
  classical
  let B := A ⊗[A₀] B₀
  let Q := B ⧸ P
  let π : B →+* Q := Ideal.Quotient.mk P
  let _ : IsDomain Q := Ideal.Quotient.isDomain P
  let fA : A →+* Q := π.comp (algebraMap A B)
  let gB : B₀ →+* Q := π.comp (Algebra.TensorProduct.includeRight : B₀ →ₐ[A₀] B).toRingHom
  have hfA_apply : ∀ a : A, fA a = π (a ⊗ₜ[A₀] (1 : B₀)) := by
    intro a
    show π (algebraMap A (A ⊗[A₀] B₀) a) = π (a ⊗ₜ[A₀] (1 : B₀))
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hgB_apply : ∀ b : B₀, gB b = π ((1 : A) ⊗ₜ[A₀] b) := fun b => rfl
  have hπ_tmul : ∀ (a : A) (b : B₀), π (a ⊗ₜ[A₀] b) = fA a * gB b := by
    intro a b
    rw [hfA_apply, hgB_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have htm : ∀ a : A₀, (algebraMap A₀ A a) ⊗ₜ[A₀] (1 : B₀) = (1 : A) ⊗ₜ[A₀] (algebraMap A₀ B₀ a) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hfA0 : ∀ a ∈ maximalIdeal A, fA a = 0 := by
    intro a ha
    rw [hfA_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr (hPA a ha)
  let fκ : ResidueField A →+* Q := Ideal.Quotient.lift (maximalIdeal A) fA hfA0
  have hfκ : ∀ a : A, fκ (residue A a) = fA a := fun a => Ideal.Quotient.lift_mk (maximalIdeal A) fA hfA0
  let _ : Algebra (ResidueField A) Q := fκ.toAlgebra' (fun c x => mul_comm (fκ c) x)
  have halgQ : ∀ a : A, algebraMap (ResidueField A) Q (residue A a) = fA a := hfκ
  have hgB0 : ∀ b ∈ 𝔪₀, gB b = 0 := by
    intro b hb
    rw [hgB_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr (hP₀ b hb)
  let gk : (B₀ ⧸ 𝔪₀) →+* Q := Ideal.Quotient.lift 𝔪₀ gB hgB0
  have hgk : ∀ b : B₀, gk (Ideal.Quotient.mk 𝔪₀ b) = gB b := fun b => Ideal.Quotient.lift_mk 𝔪₀ gB hgB0
  let _ : Field (B₀ ⧸ 𝔪₀) := Ideal.Quotient.field 𝔪₀
  have hφ₀ : ∀ a ∈ maximalIdeal A₀, ((Ideal.Quotient.mk 𝔪₀).comp (algebraMap A₀ B₀)) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr (h𝔪₀ a ha)
  let φ₀ : ResidueField A₀ →+* (B₀ ⧸ 𝔪₀) := Ideal.Quotient.lift (maximalIdeal A₀) _ hφ₀
  have hφ₀_apply : ∀ a : A₀, φ₀ (residue A₀ a) = Ideal.Quotient.mk 𝔪₀ (algebraMap A₀ B₀ a) :=
    fun a => Ideal.Quotient.lift_mk (maximalIdeal A₀) _ hφ₀
  let _ : Algebra (ResidueField A₀) (B₀ ⧸ 𝔪₀) := φ₀.toAlgebra' (fun c x => mul_comm (φ₀ c) x)
  have halgk : ∀ a : A₀, algebraMap (ResidueField A₀) (B₀ ⧸ 𝔪₀) (residue A₀ a) =
      Ideal.Quotient.mk 𝔪₀ (algebraMap A₀ B₀ a) := hφ₀_apply
  let _ : IsScalarTower A₀ (ResidueField A₀) (B₀ ⧸ 𝔪₀) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (halgk a).symm)
  let _ : Algebra.FiniteType A₀ (B₀ ⧸ 𝔪₀) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A₀ 𝔪₀) (Ideal.Quotient.mkₐ_surjective A₀ 𝔪₀)
  let _ : Algebra.FiniteType (ResidueField A₀) (B₀ ⧸ 𝔪₀) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A₀ (ResidueField A₀) (B₀ ⧸ 𝔪₀)
  let _ : Module.Finite (ResidueField A₀) (B₀ ⧸ 𝔪₀) :=
    finite_of_finite_type_of_isJacobsonRing (ResidueField A₀) (B₀ ⧸ 𝔪₀)
  have hsq : (algebraMap (ResidueField A) Q).comp (ResidueField.map (algebraMap A₀ A)) =
      gk.comp (algebraMap (ResidueField A₀) (B₀ ⧸ 𝔪₀)) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 : ResidueField.map (algebraMap A₀ A) (residue A₀ a) = residue A (algebraMap A₀ A a) :=
      ResidueField.map_residue (algebraMap A₀ A) a
    rw [RingHom.comp_apply, RingHom.comp_apply, h1, halgQ, halgk, hgk, hfA_apply, hgB_apply, htm]
  have hgint : ∀ b : B₀, IsIntegral (ResidueField A) (gB b) := by
    intro b
    have h1 : IsIntegral (ResidueField A₀) (Ideal.Quotient.mk 𝔪₀ b) :=
      _root_.IsIntegral.of_finite (ResidueField A₀) (Ideal.Quotient.mk 𝔪₀ b)
    have h2 : IsIntegral (ResidueField A) (gk (Ideal.Quotient.mk 𝔪₀ b)) :=
      h1.map_of_comp_eq (ResidueField.map (algebraMap A₀ A)) gk hsq
    rwa [hgk] at h2
  let _ : Algebra.IsIntegral (ResidueField A) Q := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      have h1 : IsIntegral (ResidueField A) (fA a) := by
        rw [← halgQ]
        apply isIntegral_algebraMap
      have h2 := @_root_.IsIntegral.mul (ResidueField A) Q _ _ _ _ _ h1 (hgint b)
      rw [hπ_tmul]
      apply h2
    | add x y hx hy =>
      have h3 := @_root_.IsIntegral.add (ResidueField A) Q _ _ _ _ _ hx hy
      rw [map_add]
      apply h3
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField A) (K := Q)
  let e : ResidueField A ≃+* Q := RingEquiv.ofBijective (algebraMap (ResidueField A) Q) hbij
  have he : ∀ a : A, e (residue A a) = fA a := halgQ
  let χ : B₀ →+* ResidueField A := e.symm.toRingHom.comp gB
  have hχ : ∀ b : B₀, e (χ b) = gB b := fun b => e.apply_symm_apply (gB b)
  have hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a) := by
    intro a
    apply e.injective
    rw [hχ, he, hgB_apply, hfA_apply, htm]
  refine ⟨χ, hχA₀, ?_⟩
  dsimp only
  ext t
  rw [RingHom.mem_ker]
  have key : ∀ t : B, (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
      ({ toRingHom := χ
         commutes' := by
           intro a
           rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]
           apply hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
      (fun _ _ => Commute.all _ _)).toRingHom t = e.symm (π t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, hπ_tmul, map_mul]
      congr 1
      apply e.injective
      rw [e.apply_symm_apply, IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq, he]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
  rw [key, map_eq_zero_iff _ e.symm.injective]
  apply (Ideal.Quotient.eq_zero_iff_mem).symm


-- created on 2026-10-13
