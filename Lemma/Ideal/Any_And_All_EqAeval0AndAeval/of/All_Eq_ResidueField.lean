import Mathlib
import Initialize.Tactic.Attr.Basic
open KaehlerDifferential
open MvPolynomial (pderiv X pderiv_X)
open scoped TensorProduct


private lemma exists_derivation_of_surjective
  [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (f : P →ₐ[R] S) (d : P →ₗ[R] M)
-- given
  (hf : Function.Surjective f)
  (hleib : ∀ p q, d (p * q) = f p • d q + f q • d p)
  (hker : ∀ p, f p = 0 → d p = 0) :
-- imply
  ∃ δ : Derivation R S M, ∀ p, δ (f p) = d p := by
-- proof
  have hwd : ∀ p q, f p = f q → d p = d q := by
    intro p q hpq
    have : d (p - q) = 0 := hker _ (by rw [map_sub, hpq, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let σ := Function.surjInv hf
  have hσ : ∀ s, f (σ s) = s := Function.surjInv_eq hf
  let δ₀ : S →ₗ[R] M :=
    { toFun := fun s => d (σ s)
      map_add' := fun s t => by
        change d (σ (s + t)) = d (σ s) + d (σ t)
        rw [← map_add]
        apply hwd
        rw [hσ, map_add, hσ, hσ]
      map_smul' := fun c s => by
        change d (σ (c • s)) = c • d (σ s)
        rw [← map_smul]
        apply hwd
        rw [hσ, map_smul, hσ] }
  have hδ₀ : ∀ p, δ₀ (f p) = d p := fun p => hwd _ _ (hσ _)
  have h1 : d 1 = 0 := by
    have := hleib 1 1
    rw [mul_one, show f 1 = 1 from map_one f, one_smul] at this
    apply add_left_cancel
    rw [add_zero]
    apply this.symm
  refine ⟨{ toLinearMap := δ₀
            map_one_eq_zero' := ?_
            leibniz' := ?_ }, hδ₀⟩
  ·
    change δ₀ 1 = 0
    rw [← map_one f]
    apply (hδ₀ 1).trans h1
  ·
    intro a b
    change d (σ (a * b)) = a • d (σ b) + b • d (σ a)
    rw [hwd (σ (a * b)) (σ a * σ b) (by rw [hσ, map_mul, hσ, hσ]), hleib, hσ, hσ]


/--
[Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField.lean)
-/
@[path]
private lemma main
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
  {u : Ideal S} [u.IsPrime]
  {ι : Type} [Finite ι]
  {w : ι → S}
  {b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R])}
-- given
  (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
-- imply
  ∃ (m : ℕ) (x : Fin m → S) (h : Fin m → MvPolynomial (ι ⊕ Fin m) R), Function.Surjective (MvPolynomial.aeval (Sum.elim w x) : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S) ∧ (∀ a, MvPolynomial.aeval (Sum.elim w x) (h a) = 0) ∧ MvPolynomial.aeval (Sum.elim w x) (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))) ∉ u := by
-- proof
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  set m := s.card
  let x : Fin m → S := fun a => (s.equivFin.symm a : S)
  let f : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S := MvPolynomial.aeval (Sum.elim w x)
  have hf : Function.Surjective f := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff, ← hs]
    apply Algebra.adjoin_mono
    intro y hy
    refine ⟨Sum.inr (s.equivFin ⟨y, hy⟩), ?_⟩
    simp [x]
  let κ := u.ResidueField
  let Xgrad : MvPolynomial (ι ⊕ Fin m) R → (Fin m → κ) := fun p b => algebraMap S κ (f (pderiv (Sum.inr b) p))
  have Xgrad_add : ∀ p q, Xgrad (p + q) = Xgrad p + Xgrad q := by
    intro p q
    funext b
    simp [Xgrad, map_add, Pi.add_apply]
  have Xgrad_smul : ∀ (c : R) p, Xgrad (c • p) = c • Xgrad p := by
    intro c p
    funext b
    change algebraMap S κ (f (pderiv (Sum.inr b) (c • p))) = c • algebraMap S κ (f (pderiv (Sum.inr b) p))
    rw [Derivation.map_smul, map_smul, Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R S κ]
  have Xgrad_mul : ∀ p q, Xgrad (p * q) = algebraMap S κ (f p) • Xgrad q + algebraMap S κ (f q) • Xgrad p := by
    intro p q
    funext b
    simp [Xgrad, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Pi.add_apply, Pi.smul_apply]
    rw [Algebra.smul_def, Algebra.smul_def]
  have Xgrad_X_inl : ∀ i, Xgrad (X (Sum.inl i)) = 0 := by
    intro i
    funext b
    simp [Xgrad, pderiv_X]
  have Xgrad_X_inr : ∀ b, Xgrad (X (Sum.inr b)) = Pi.single b 1 := by
    intro b
    funext b'
    simp [Xgrad, pderiv_X, Pi.single_apply, Sum.inr.injEq]
    if hb : b = b' then
      subst hb
      simp
    else
      rw [ite_eq_right hb, ite_eq_right (fun h => hb h.symm)]
  let t : Set (Fin m → κ) := Set.range fun p : ↥(RingHom.ker f.toRingHom) => Xgrad p.1
  have hspan : Submodule.span κ t = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hφt : ∀ p : MvPolynomial (ι ⊕ Fin m) R, f p = 0 → φ (Xgrad p) = 0 := by
      intro p hp
      have : φ (Xgrad p) ∈ (Submodule.span κ t).map φ := Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)
      rwa [hφ, Submodule.mem_bot] at this
    let d : MvPolynomial (ι ⊕ Fin m) R →ₗ[R] κ :=
      { toFun := fun p => φ (Xgrad p)
        map_add' := fun p q => by
          rw [Xgrad_add, map_add]
        map_smul' := fun c p => by
          rw [Xgrad_smul, LinearMap.map_smul_of_tower]
          rfl }
    have hd : ∀ p, d p = φ (Xgrad p) := fun p => rfl
    obtain ⟨δ, hδ⟩ := exists_derivation_of_surjective f d hf
      (fun p q => by
        rw [hd, hd, hd, Xgrad_mul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def])
      (fun p hp => hφt p hp)
    let ℓ : Ω[S⁄R] →ₗ[S] κ := δ.liftKaehlerDifferential
    let L : κ ⊗[S] Ω[S⁄R] →ₗ[κ] κ := ℓ.liftBaseChange κ
    have hL : L = 0 := by
      refine b₀.ext fun i => ?_
      rw [hb₀ i, LinearMap.zero_apply]
      change (1 : κ) • ℓ (D R S (w i)) = 0
      rw [one_smul]
      change δ.liftKaehlerDifferential (D R S (w i)) = 0
      rw [Derivation.liftKaehlerDifferential_comp_D]
      have : f (X (Sum.inl i)) = w i := by
        simp [f]
      rw [← this, hδ, hd, Xgrad_X_inl, map_zero]
    have hφb : ∀ b, φ (Pi.single b 1) = 0 := by
      intro b
      have h1 : L ((1 : κ) ⊗ₜ[S] D R S (x b)) = 0 := by
        rw [hL, LinearMap.zero_apply]
      change (1 : κ) • ℓ (D R S (x b)) = 0 at h1
      rw [one_smul] at h1
      change δ.liftKaehlerDifferential (D R S (x b)) = 0 at h1
      rw [Derivation.liftKaehlerDifferential_comp_D] at h1
      have : f (X (Sum.inr b)) = x b := by
        simp [f]
      rw [← this, hδ, hd, Xgrad_X_inr] at h1
      apply h1
    apply hφ0
    refine (Pi.basisFun κ (Fin m)).ext fun b => ?_
    rw [Pi.basisFun_apply, LinearMap.zero_apply]
    apply hφb b
  obtain ⟨bs, hbt, hbspan, hli⟩ := exists_linearIndependent κ t
  rw [hspan] at hbspan
  let B : Module.Basis bs κ (Fin m → κ) := Module.Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan])
  have : Finite bs := Module.Finite.finite_basis B
  have : Fintype bs := Fintype.ofFinite bs
  have hcard : Fintype.card bs = m := by
    have := Module.finrank_eq_card_basis B
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    apply this.symm
  let e : bs ≃ Fin m := Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])
  have hmem : ∀ a : Fin m, ∃ p : ↥(RingHom.ker f.toRingHom), Xgrad p.1 = (e.symm a : Fin m → κ) :=
    fun a => hbt (e.symm a).2
  choose hp hhp using hmem
  let h : Fin m → MvPolynomial (ι ⊕ Fin m) R := fun a => (hp a).1
  refine ⟨m, x, h, hf, fun a => (hp a).2, ?_⟩
  set N : Matrix (Fin m) (Fin m) (MvPolynomial (ι ⊕ Fin m) R) := Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)
  have hrow : (N.map ((algebraMap S κ).comp f.toRingHom)) = Matrix.of fun a => (e.symm a : Fin m → κ) := by
    ext a b
    change algebraMap S κ (f (pderiv (Sum.inr b) (h a))) = (e.symm a : Fin m → κ) b
    rw [← hhp a]
  have hliRows : LinearIndependent κ (N.map ((algebraMap S κ).comp f.toRingHom)).row := by
    rw [hrow]
    change LinearIndependent κ (fun a => ((e.symm a : bs) : Fin m → κ))
    have hB : (fun a => ((e.symm a : bs) : Fin m → κ)) = ⇑B ∘ ⇑e.symm := by
      funext a
      simp [B]
    rw [hB]
    apply B.linearIndependent.comp e.symm e.symm.injective
  have hunit : IsUnit (N.map ((algebraMap S κ).comp f.toRingHom)) := Matrix.linearIndependent_rows_iff_isUnit.mp hliRows
  have hdet : (N.map ((algebraMap S κ).comp f.toRingHom)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hdet' : ((algebraMap S κ).comp f.toRingHom) N.det ≠ 0 := by
    rw [RingHom.map_det]
    apply hdet
  intro hmemu
  apply hdet'
  change algebraMap S κ (f N.det) = 0
  apply Ideal.algebraMap_residueField_eq_zero.mpr hmemu


-- created on 2026-10-13
