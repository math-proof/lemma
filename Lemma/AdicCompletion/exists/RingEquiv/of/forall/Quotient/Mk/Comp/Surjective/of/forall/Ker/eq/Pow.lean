import Mathlib
import sympy.Basic

/-!
Port of FLT AssemblyProof helpers for the AdicCompletion ring-equiv criterion.
-/

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem factorPow_evalₐ (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have h : c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := c.2 hle
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
  have h' : c n - c m ∈ I ^ m := by
    have := Submodule.neg_mem _ h
    rwa [neg_sub] at this
  exact Ideal.Quotient.eq.mpr h'

variable (I : Ideal R) (J : Ideal S) (f : R →+* S)
  (hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (J ^ k)).comp f) = I ^ k)
  (hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ k)).comp f))

private noncomputable def ψ (k : ℕ) : R ⧸ I ^ k →+* S ⧸ J ^ k :=
  Ideal.Quotient.lift (I ^ k) ((Ideal.Quotient.mk (J ^ k)).comp f)
    (fun r hr => by rw [← RingHom.mem_ker, hker]; exact hr)

private theorem ψ_mk (k : ℕ) (r : R) :
    ψ I J f hker k (Ideal.Quotient.mk (I ^ k) r) = Ideal.Quotient.mk (J ^ k) (f r) :=
  Ideal.Quotient.lift_mk _ _ _

private theorem ψ_injective (k : ℕ) : Function.Injective (ψ I J f hker k) :=
  RingHom.lift_injective_of_ker_le_ideal (I ^ k) _ (le_of_eq (hker k))

private theorem factorPow_comp_ψ {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (ψ I J f hker n) =
      (ψ I J f hker m).comp (Ideal.Quotient.factorPow I hle) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, ψ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

include hsurj in
private theorem ψ_surjective (k : ℕ) : Function.Surjective (ψ I J f hker k) :=
  Ideal.Quotient.lift_surjective_of_surjective (I ^ k) _ (hsurj k)

private noncomputable def e (k : ℕ) : R ⧸ I ^ k ≃+* S ⧸ J ^ k :=
  RingEquiv.ofBijective (ψ I J f hker k) ⟨ψ_injective I J f hker k, ψ_surjective I J f hker hsurj k⟩

private theorem e_apply (k : ℕ) (q : R ⧸ I ^ k) : e I J f hker hsurj k q = ψ I J f hker k q := rfl

private theorem compatF {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp ((ψ I J f hker n).comp (AdicCompletion.evalₐ I n).toRingHom) =
      (ψ I J f hker m).comp (AdicCompletion.evalₐ I m).toRingHom := by
  rw [← RingHom.comp_assoc, factorPow_comp_ψ, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun x => factorPow_evalₐ I hle x

private noncomputable def F : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J (fun n => (ψ I J f hker n).comp (AdicCompletion.evalₐ I n).toRingHom)
    (fun hle => compatF I J f hker hle)

private theorem evalₐ_F (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (F I J f hker x) = ψ I J f hker n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (fun hle => compatF I J f hker hle) n x

private theorem compatG {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp
        ((e I J f hker hsurj n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) =
      (e I J f hker hsurj m).symm.toRingHom.comp (AdicCompletion.evalₐ J m).toRingHom := by
  refine RingHom.ext fun y => ?_
  apply (e I J f hker hsurj m).injective
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [e_apply, ← RingHom.comp_apply (ψ I J f hker m), ← factorPow_comp_ψ I J f hker hle,
    RingHom.comp_apply, ← e_apply I J f hker hsurj n, RingEquiv.apply_symm_apply,
    factorPow_evalₐ]

private noncomputable def G : AdicCompletion J S →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (fun n => (e I J f hker hsurj n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom)
    (fun hle => compatG I J f hker hsurj hle)

private theorem evalₐ_G (n : ℕ) (y : AdicCompletion J S) :
    AdicCompletion.evalₐ I n (G I J f hker hsurj y) =
      (e I J f hker hsurj n).symm (AdicCompletion.evalₐ J n y) :=
  AdicCompletion.evalₐ_liftRingHom I _ (fun hle => compatG I J f hker hsurj hle) n y

private theorem F_comp_G : (F I J f hker).comp (G I J f hker hsurj) = RingHom.id _ := by
  refine RingHom.ext fun y => AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, evalₐ_F, evalₐ_G, ← e_apply I J f hker hsurj n,
    RingEquiv.apply_symm_apply, RingHom.id_apply]

private theorem G_comp_F : (G I J f hker hsurj).comp (F I J f hker) = RingHom.id _ := by
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, evalₐ_G, evalₐ_F, ← e_apply I J f hker hsurj n,
    RingEquiv.symm_apply_apply, RingHom.id_apply]

/--
[AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.lean)
-/
@[path]
private lemma main
  {R S : Type*} [CommRing R] [CommRing S]
-- given
  (I : Ideal R) (J : Ideal S) (f : R →+* S)
  (hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (J ^ k)).comp f))
  (hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (J ^ k)).comp f) = I ^ k) :
-- imply
  ∃ e : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r : R, e (algebraMap R (AdicCompletion I R) r) =
        algebraMap S (AdicCompletion J S) (f r) := by
-- proof
  refine ⟨RingEquiv.ofRingHom (F I J f hker) (G I J f hker hsurj)
      (F_comp_G I J f hker hsurj) (G_comp_F I J f hker hsurj), fun r => ?_⟩
  show F I J f hker (algebraMap R (AdicCompletion I R) r) =
    algebraMap S (AdicCompletion J S) (f r)
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_F, AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq, ψ_mk]


-- created on 2026-10-09
