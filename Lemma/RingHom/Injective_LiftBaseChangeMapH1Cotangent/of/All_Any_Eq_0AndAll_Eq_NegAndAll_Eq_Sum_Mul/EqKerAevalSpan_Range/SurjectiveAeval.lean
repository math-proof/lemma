import Mathlib
import sympy.Basic
open Algebra Algebra.Generators Algebra.Extension
open MvPolynomial (rename C sumRingEquiv sumRingEquiv_symm_C_C sumRingEquiv_symm_C_X algebraMap_eq
  ringHom_ext aeval)
open scoped Pointwise TensorProduct
set_option backward.isDefEq.respectTransparency false


private def IsAlt {n : ℕ} {M : Type*} [AddCommGroup M] (d : Fin n → Fin n → M) : Prop :=
  (∀ j, d j j = 0) ∧ ∀ j l, d j l = - d l j

private lemma sum_sum_smul_eq_zero_of_isAlt
  {A : Type*} [CommRing A] {n : ℕ} {M : Type*} [AddCommGroup M] [Module A M]
  (a : Fin n → A) (d : Fin n → Fin n → M) (hd : IsAlt d) :
  ∑ j, ∑ l, (a j * a l) • d j l = 0 := by
  classical
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun j l => (a j * a l) • d j l)]
  refine Finset.sum_ninvolution (fun p => p.swap) ?_ ?_
    (fun p => Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
    (fun p => Prod.swap_swap p)
  ·
    intro p
    obtain ⟨j, l⟩ := p
    simp only [Prod.swap_prod_mk]
    rw [hd.2 l j, mul_comm (a l) (a j), smul_neg, add_neg_cancel]
  ·
    intro p hp heq
    apply hp
    obtain ⟨j, l⟩ := p
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp only [hd.1, smul_zero]

private lemma exists_isAlt_lift
  {n : ℕ} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (π : M →+ N) (hπ : Function.Surjective π) (d : Fin n → Fin n → N) (hd : IsAlt d) :
  ∃ D : Fin n → Fin n → M, IsAlt D ∧ ∀ j l, π (D j l) = d j l := by
  classical
  choose L hL using hπ
  refine ⟨fun j l => if j < l then L (d j l) else if l < j then - L (d l j) else 0, ⟨?_, ?_⟩, ?_⟩
  ·
    intro j
    simp
  ·
    intro j l
    cases lt_trichotomy j l with
    | inl h =>
      simp [h, not_lt.mpr h.le]
    | inr h =>
      cases h with
      | inl h =>
        cases h
        simp
      | inr h =>
        simp [h, not_lt.mpr h.le]
  ·
    intro j l
    cases lt_trichotomy j l with
    | inl h =>
      simp [h, hL]
    | inr h =>
      cases h with
      | inl h =>
        cases h
        simp [hd.1 j]
      | inr h =>
        simp [h, not_lt.mpr h.le, hL, ← hd.2 j l]

private def HasKoszulSyzygies {A : Type*} [CommRing A] {n : ℕ} (r : Fin n → A) : Prop :=
  ∀ m : Fin n → A, ∑ j, r j * m j = 0 →
    ∃ d : Fin n → Fin n → A, IsAlt d ∧ ∀ j, m j = ∑ l, r l * d j l

private lemma exists_sum_eq_of_mem_span_range_mul
  {A : Type*} [CommRing A] {n : ℕ} (v : Fin n → A) (N : Ideal A) {x : A}
  (hx : x ∈ Ideal.span (Set.range v) * N) :
  ∃ m : Fin n → N, x = ∑ j, v j * m j := by
  classical
  refine Submodule.mul_induction_on hx ?_ ?_
  ·
    intro a ha b hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
    refine ⟨fun j => ⟨c j * b, N.mul_mem_left _ hb⟩, ?_⟩
    simp only [Finset.sum_mul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  ·
    intro x y hx hy
    obtain ⟨m₁, rfl⟩ := hx
    obtain ⟨m₂, rfl⟩ := hy
    refine ⟨fun j => m₁ j + m₂ j, ?_⟩
    simp only [Submodule.coe_add, mul_add, Finset.sum_add_distrib]

private lemma ker_inf_sq_le_ker_mul
  {A B : Type*} [CommRing A] [CommRing B]
  (φ : A →+* B) (hφ : Function.Surjective φ) {n : ℕ} (r : Fin n → B)
  (hsyz : HasKoszulSyzygies r) :
  RingHom.ker φ ⊓ (Ideal.comap φ (Ideal.span (Set.range r))) ^ 2 ≤
    RingHom.ker φ * Ideal.comap φ (Ideal.span (Set.range r)) := by
  classical
  choose rt hrt using fun j => hφ (r j)
  set I' := RingHom.ker φ with hI'
  set F : Ideal A := Ideal.span (Set.range rt) with hF
  have hmapF : F.map φ = Ideal.span (Set.range r) := by
    rw [hF, Ideal.map_span, ← Set.range_comp]
    have : (⇑φ ∘ rt) = r := funext fun j => hrt j
    rw [this]
  have hJ : Ideal.comap φ (Ideal.span (Set.range r)) = F ⊔ I' := by
    rw [← hmapF, Ideal.comap_map_of_surjective φ hφ, hI', ← RingHom.ker_eq_comap_bot]
  set J := Ideal.comap φ (Ideal.span (Set.range r)) with hJdef
  have hI'J : I' ≤ J := by
    rw [hJ]
    apply le_sup_right
  have hFJ : F ≤ J := by
    rw [hJ]
    apply le_sup_left
  have hsq : J ^ 2 ≤ I' * J ⊔ F ^ 2 := by
    rw [pow_two, pow_two]
    conv_lhs => rw [hJ]
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · apply le_sup_right
    ·
      rw [mul_comm]
      apply le_sup_of_le_left (Ideal.mul_mono_right hFJ)
    · apply le_sup_of_le_left (Ideal.mul_mono_right hFJ)
    · apply le_sup_of_le_left (Ideal.mul_mono_right hI'J)
  intro x hx
  obtain ⟨hxI, hxJ⟩ := hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hsq hxJ)
  have hzI : z ∈ I' := by
    have : y ∈ I' := Ideal.mul_le_left hy
    simpa using (Submodule.sub_mem _ hxI this)
  refine Submodule.add_mem _ hy ?_
  rw [pow_two, hF] at hz
  obtain ⟨m, rfl⟩ := exists_sum_eq_of_mem_span_range_mul rt (Ideal.span (Set.range rt)) hz
  have hrel : ∑ j, r j * φ (m j) = 0 := by
    have := (RingHom.mem_ker).mp (hI' ▸ hzI)
    simpa only [map_sum, map_mul, hrt] using this
  obtain ⟨dB, hdB, hmdB⟩ := hsyz (fun j => φ (m j)) hrel
  obtain ⟨D, hD, hDD⟩ := exists_isAlt_lift φ.toAddMonoidHom hφ dB hdB
  have he : ∀ j, (m j : A) - ∑ l, rt l * D j l ∈ I' := by
    intro j
    rw [hI', RingHom.mem_ker, map_sub, map_sum]
    simp only [map_mul, hrt]
    change φ (m j) - ∑ l, r l * φ.toAddMonoidHom (D j l) = 0
    simp only [hDD, hmdB j, sub_self]
  have hsplit : ∑ j, rt j * (m j : A) =
      ∑ j, rt j * ((m j : A) - ∑ l, rt l * D j l) + ∑ j, ∑ l, (rt j * rt l) • D j l := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, smul_eq_mul, mul_assoc]
    abel
  rw [hsplit, sum_sum_smul_eq_zero_of_isAlt rt D hD, add_zero]
  refine Ideal.sum_mem _ fun j _ => ?_
  apply Ideal.mul_mem_mul_rev (he j) (hFJ (Ideal.subset_span ⟨j, rfl⟩))

private noncomputable instance compAlgebra
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  Algebra P.Ring (Q.comp P).Ring :=
  ((Q.toComp P).toAlgHom : P.Ring →+* (Q.comp P).Ring).toAlgebra

private lemma compAlgebra_algebraMap_apply
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) (p : P.Ring) :
  algebraMap P.Ring (Q.comp P).Ring p = rename Sum.inr p := by
  change (Q.toComp P).toAlgHom p = _
  rw [Generators.toComp_toAlgHom]

private lemma compAlgebra_smul_def
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) (p : P.Ring) (q : (Q.comp P).Ring) :
  p • q = rename Sum.inr p * q := by
  rw [Algebra.smul_def, compAlgebra_algebraMap_apply]

private noncomputable def compLinearEquiv
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  MvPolynomial ι P.Ring ≃ₗ[P.Ring] (Q.comp P).Ring where
  toFun := (sumRingEquiv R ι σ).symm
  invFun := sumRingEquiv R ι σ
  map_add' := map_add _
  map_smul' p f := by
    rw [RingHom.id_apply, compAlgebra_smul_def, Algebra.smul_def, map_mul, algebraMap_eq]
    congr 1
    change (((sumRingEquiv R ι σ).symm : MvPolynomial ι P.Ring →+* (Q.comp P).Ring).comp
        (C : P.Ring →+* MvPolynomial ι P.Ring)) p = rename Sum.inr p
    congr 1
    refine ringHom_ext (fun r => ?_) (fun s => ?_)
    ·
      rw [RingHom.comp_apply, RingHom.coe_coe, sumRingEquiv_symm_C_C]
      apply (MvPolynomial.rename_C (Sum.inr (β := σ) (α := ι)) r).symm
    ·
      rw [RingHom.comp_apply, RingHom.coe_coe, sumRingEquiv_symm_C_X]
      apply (MvPolynomial.rename_X (Sum.inr (β := σ) (α := ι)) s).symm
  left_inv p := (sumRingEquiv R ι σ).apply_symm_apply p
  right_inv p := (sumRingEquiv R ι σ).symm_apply_apply p

private instance compAlgebra_free
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  Module.Free P.Ring (Q.comp P).Ring :=
  Module.Free.of_equiv (compLinearEquiv Q P)

private instance compAlgebra_flat
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  Module.Flat P.Ring (Q.comp P).Ring :=
  inferInstance

private noncomputable def nu
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  (Q.comp P).Ring ⊗[P.Ring] P.ker →ₗ[P.Ring] (Q.comp P).Ring :=
  LinearMap.comp (TensorProduct.rid P.Ring (Q.comp P).Ring).toLinearMap
    (P.ker.subtype.lTensor (Q.comp P).Ring)

private lemma nu_tmul
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  (q : (Q.comp P).Ring) (a : P.ker) :
  nu Q P (q ⊗ₜ a) = rename Sum.inr (a : P.Ring) * q := by
  simp only [nu, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, Submodule.coe_subtype, TensorProduct.rid_tmul, compAlgebra_smul_def]

private lemma nu_injective
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  Function.Injective (nu Q P) := by
  refine (TensorProduct.rid P.Ring (Q.comp P).Ring).injective.comp ?_
  apply Module.Flat.lTensor_preserves_injective_linearMap _ P.ker.injective_subtype

private lemma map_toComp_le_ker
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  P.ker.map (Q.toComp P).toAlgHom ≤ (Q.comp P).ker := by
  rw [Q.ker_comp_eq_sup P]
  apply le_sup_left

private lemma nu_mem_map
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  (y : (Q.comp P).Ring ⊗[P.Ring] P.ker) :
  nu Q P y ∈ P.ker.map (Q.toComp P).toAlgHom := by
  induction y using TensorProduct.inductionOn with
  | tmul q a =>
    rw [nu_tmul]
    rw [← Generators.toComp_toAlgHom Q P]
    apply Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (Q.toComp P).toAlgHom a.2)
  | add x y hx hy =>
    rw [map_add]
    apply Ideal.add_mem _ hx hy

private lemma nu_mem_ker
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  (y : (Q.comp P).Ring ⊗[P.Ring] P.ker) :
  nu Q P y ∈ (Q.comp P).ker :=
  map_toComp_le_ker Q P (nu_mem_map Q P y)

private lemma algebraMap_rename_inr
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) (p : P.Ring) :
  algebraMap (Q.comp P).Ring T (rename Sum.inr p) = algebraMap S T (algebraMap P.Ring S p) := by
  rw [Generators.algebraMap_apply, Generators.algebraMap_apply, ← toComp_toAlgHom Q P,
    Hom.algebraMap_toAlgHom]

private noncomputable def thetaAux
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) (q : (Q.comp P).Ring) :
  P.toExtension.ker →+ T ⊗[S] P.toExtension.Cotangent :=
  ((TensorProduct.mk S T P.toExtension.Cotangent)
      (algebraMap (Q.comp P).Ring T q)).toAddMonoidHom.comp
    (Extension.Cotangent.mk (P := P.toExtension)).toAddMonoidHom

private lemma thetaAux_apply
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) (q : (Q.comp P).Ring) (a : P.toExtension.ker) :
  thetaAux Q P q a = algebraMap (Q.comp P).Ring T q ⊗ₜ[S] Extension.Cotangent.mk a := rfl

private noncomputable def theta
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  (Q.comp P).Ring ⊗[P.Ring] P.ker →+ T ⊗[S] P.toExtension.Cotangent :=
  TensorProduct.liftAddHom
    { toFun := thetaAux Q P
      map_zero' := by
        ext a
        rw [thetaAux_apply, map_zero, TensorProduct.zero_tmul, AddMonoidHom.zero_apply]
      map_add' := fun q q' => by
        ext a
        rw [thetaAux_apply, map_add, TensorProduct.add_tmul, AddMonoidHom.add_apply,
          thetaAux_apply, thetaAux_apply] }
    (fun p q a => by
      change thetaAux Q P (p • q) a = thetaAux Q P q (p • a)
      rw [thetaAux_apply, thetaAux_apply, compAlgebra_smul_def, map_mul, algebraMap_rename_inr,
        (Extension.Cotangent.mk (P := P.toExtension)).map_smul p a,
        ← algebraMap_smul S p (Extension.Cotangent.mk (P := P.toExtension) a),
        ← TensorProduct.smul_tmul, Algebra.smul_def])

private lemma theta_tmul
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) (q : (Q.comp P).Ring) (a : P.ker) :
  theta Q P (q ⊗ₜ a) = algebraMap (Q.comp P).Ring T q ⊗ₜ[S] Extension.Cotangent.mk a := rfl

private lemma theta_surjective
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  Function.Surjective (theta Q P) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul t m =>
    obtain ⟨q, rfl⟩ := (Q.comp P).algebraMap_surjective t
    obtain ⟨a, rfl⟩ := Extension.Cotangent.mk_surjective m
    apply Exists.intro (q ⊗ₜ a)
    apply theta_tmul Q P q a
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    apply Exists.intro (x + y)
    apply map_add _ _ _

private noncomputable abbrev alpha
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ) :
  T ⊗[S] P.toExtension.Cotangent →ₗ[T] (Q.comp P).toExtension.Cotangent :=
  (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T

private lemma alpha_theta
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  (y : (Q.comp P).Ring ⊗[P.Ring] P.ker) :
  alpha Q P (theta Q P y) = Extension.Cotangent.mk ⟨nu Q P y, nu_mem_ker Q P y⟩ := by
  induction y using TensorProduct.inductionOn with
  | tmul q a =>
    rw [theta_tmul, LinearMap.liftBaseChange_tmul, Extension.Cotangent.map_mk, algebraMap_smul]
    apply Extension.Cotangent.ext
    rw [Extension.Cotangent.val_smul', Extension.Cotangent.val_mk, Extension.Cotangent.val_mk,
      ← LinearMap.map_smul]
    congr 1
    ext
    simp only [SetLike.val_smul, smul_eq_mul, Hom.toExtensionHom_toAlgHom_apply, nu_tmul,
      toComp_toAlgHom, mul_comm q]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, ← map_add]
    congr 1
    ext
    simp only [Submodule.coe_add, map_add]

private lemma exists_nu_eq_and_theta_eq_zero
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  {w : (Q.comp P).Ring}
  (hw : w ∈ P.ker.map (Q.toComp P).toAlgHom * (Q.comp P).ker) :
  ∃ z, nu Q P z = w ∧ theta Q P z = 0 := by
  refine Submodule.mul_induction_on hw ?_ ?_
  ·
    intro i hi j hj
    apply (fun (key : ∀ j ∈ (Q.comp P).ker, ∃ z, nu Q P z = i * j ∧ theta Q P z = 0) => key j hj)
    rw [Ideal.map] at hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    ·
      intro x hx j hj
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨j ⊗ₜ ⟨a, ha⟩, ?_, ?_⟩
      · rw [nu_tmul, ← Generators.toComp_toAlgHom Q P]
      ·
        rw [theta_tmul]
        have : algebraMap (Q.comp P).Ring T j = 0 := by
          rwa [Generators.algebraMap_apply, ← RingHom.mem_ker, ← Generators.ker_eq_ker_aeval_val]
        rw [this, TensorProduct.zero_tmul]
    ·
      intro j _
      apply Exists.intro 0
      constructor
      · rw [map_zero, zero_mul]
      · rw [map_zero]
    ·
      intro x y _ _ hx hy j hj
      obtain ⟨z₁, h₁, h₁'⟩ := hx j hj
      obtain ⟨z₂, h₂, h₂'⟩ := hy j hj
      apply Exists.intro (z₁ + z₂)
      constructor
      · rw [map_add, h₁, h₂, add_mul]
      · rw [map_add, h₁', h₂', add_zero]
    ·
      intro c x _ hx j hj
      obtain ⟨z, h, h'⟩ := hx (c * j) (Ideal.mul_mem_left _ c hj)
      refine ⟨z, ?_, h'⟩
      rw [h, smul_eq_mul]
      ring
  ·
    intro x y hx hy
    obtain ⟨z₁, h₁, h₁'⟩ := hx
    obtain ⟨z₂, h₂, h₂'⟩ := hy
    apply Exists.intro (z₁ + z₂)
    constructor
    · rw [map_add, h₁, h₂]
    · rw [map_add, h₁', h₂', add_zero]

private lemma map_ker_inf_sq_le
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  {n : ℕ} (rs : Fin n → Q.Ring) (hrs : Q.ker = Ideal.span (Set.range rs))
  (hreg : HasKoszulSyzygies rs) :
  P.ker.map (Q.toComp P).toAlgHom ⊓ (Q.comp P).ker ^ 2 ≤
    P.ker.map (Q.toComp P).toAlgHom * (Q.comp P).ker := by
  have hker : P.ker.map (Q.toComp P).toAlgHom = RingHom.ker (Q.ofComp P).toAlgHom :=
    map_toComp_ker Q P
  have hJ : (Q.comp P).ker = Ideal.comap (Q.ofComp P).toAlgHom (Ideal.span (Set.range rs)) := by
    ext x
    rw [Ideal.mem_comap, ← hrs, Generators.ker_eq_ker_aeval_val, Generators.ker_eq_ker_aeval_val,
      RingHom.mem_ker, RingHom.mem_ker, Hom.algebraMap_toAlgHom, algebraMap_self_apply]
  rw [hker, hJ]
  apply ker_inf_sq_le_ker_mul ((Q.ofComp P).toAlgHom : (Q.comp P).Ring →+* Q.Ring)
    (toAlgHom_ofComp_surjective Q P) rs hreg

private lemma alpha_injective
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  {n : ℕ} (rs : Fin n → Q.Ring)
  (hrs : Q.ker = Ideal.span (Set.range rs)) (hreg : HasKoszulSyzygies rs) :
  Function.Injective (alpha Q P) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := theta_surjective Q P x
  rw [alpha_theta, Extension.Cotangent.mk_eq_zero_iff] at hx
  have hmem : nu Q P y ∈ P.ker.map (Q.toComp P).toAlgHom ⊓ (Q.comp P).ker ^ 2 :=
    ⟨nu_mem_map Q P y, hx⟩
  obtain ⟨z, hz, hz'⟩ :=
    exists_nu_eq_and_theta_eq_zero Q P (map_ker_inf_sq_le Q P rs hrs hreg hmem)
  have hyz : y = z := nu_injective Q P (by rw [hz])
  rw [hyz, hz']

private lemma h1_liftBaseChange_injective
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Module.Flat S T]
  {ι : Type w₁} {σ : Type w₂}
  (Q : Algebra.Generators S T ι) (P : Algebra.Generators R S σ)
  {n : ℕ} (rs : Fin n → Q.Ring)
  (hrs : Q.ker = Ideal.span (Set.range rs)) (hreg : HasKoszulSyzygies rs) :
  Function.Injective
    ((Extension.H1Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T) := by
  set L := (Extension.H1Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T with hL
  have hcomm : ∀ x, (Q.comp P).toExtension.h1Cotangentι (L x) =
      alpha Q P ((P.toExtension.h1Cotangentι).lTensor T x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t x =>
      rw [hL, LinearMap.liftBaseChange_tmul, map_smul, LinearMap.lTensor_tmul,
        LinearMap.liftBaseChange_tmul]
      congr 1
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  have hflat : Function.Injective ((P.toExtension.h1Cotangentι).lTensor T) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Extension.h1Cotangentι_injective
  intro x y hxy
  apply hflat (alpha_injective Q P rs hrs hreg _)
  rw [← hcomm, ← hcomm, hxy]

private lemma h1_main
  {R : Type u₁} {S : Type u₂} {T : Type u₃}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Module.Flat S T]
  {ι : Type w₁} (val : ι → T)
  (hval : Function.Surjective (aeval val : MvPolynomial ι S →ₐ[S] T))
  {n : ℕ} (rs : Fin n → MvPolynomial ι S)
  (hker : RingHom.ker (aeval val : MvPolynomial ι S →ₐ[S] T) = Ideal.span (Set.range rs))
  (hreg : HasKoszulSyzygies rs) :
  Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
  let Q : Algebra.Generators S T ι := Algebra.Generators.ofSurjective val hval
  let P : Algebra.Generators R S S := Algebra.Generators.self R S
  have hrs : Q.ker = Ideal.span (Set.range rs) := by
    rw [Generators.ker_eq_ker_aeval_val]
    apply hker
  have hinj := h1_liftBaseChange_injective Q P rs hrs hreg
  let d : ((Q.comp P).toExtension).Hom (Algebra.Generators.self R T).toExtension :=
    (Algebra.Generators.defaultHom (Q.comp P) (Algebra.Generators.self R T)).toExtensionHom
  let d' : (Algebra.Generators.self R T).toExtension.Hom (Q.comp P).toExtension :=
    (Algebra.Generators.defaultHom (Algebra.Generators.self R T) (Q.comp P)).toExtensionHom
  have hfac : Algebra.H1Cotangent.map R R S T =
      LinearMap.comp ((Extension.H1Cotangent.map d).restrictScalars S)
        (Extension.H1Cotangent.map (Q.toComp P).toExtensionHom) := by
    rw [Algebra.H1Cotangent.map, ← Extension.H1Cotangent.map_comp]
    apply Extension.H1Cotangent.map_eq _ _
  have hfac' : ∀ x, (Algebra.H1Cotangent.map R R S T).liftBaseChange T x =
      Extension.H1Cotangent.map d
        (((Extension.H1Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T) x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t x =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul, hfac,
        LinearMap.comp_apply]
      rfl
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  have hd : Function.Injective (Extension.H1Cotangent.map d) :=
    (Extension.H1Cotangent.equiv d d').injective
  intro x y hxy
  rw [hfac', hfac'] at hxy
  apply hinj (hd hxy)

/--
[Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {S : Type v} [CommRing S] [Algebra R S]
  {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Flat S T]
  {ι : Type w'}
  {x : ι → T}
  {n : ℕ}
  {f : Fin n → MvPolynomial ι S}
-- given
  (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T))
  (hf : RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T) =
    Ideal.span (Set.range f))
  (hsyz : ∀ c : Fin n → MvPolynomial ι S, ∑ j, c j * f j = 0 →
    ∃ d : Fin n → Fin n → MvPolynomial ι S,
      (∀ j, d j j = 0) ∧ (∀ j l, d j l = -d l j) ∧ ∀ j, c j = ∑ l, f l * d j l) :
-- imply
  Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
-- proof
  apply h1_main x hx f hf
  intro m hm
  obtain ⟨d, h1, h2, h3⟩ := hsyz m (by simpa only [mul_comm] using hm)
  apply Exists.intro d
  constructor
  ·
    constructor
    · apply h1
    · apply h2
  · apply h3


-- created on 2026-10-20
