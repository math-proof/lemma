import Mathlib
import sympy.Basic
open TensorProduct
open AlgHom


/--
[AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi.lean)
-/

private lemma exists_eq_evalAlgHom {Ω : Type*} [Field Ω] {d : ℕ} (F : (Fin d → Ω) →ₐ[Ω] Ω) :
  ∃ j : Fin d, F = Pi.evalAlgHom Ω (fun _ => Ω) j := by
  classical
  have hidem : ∀ j, F (Pi.single j 1) = 0 ∨ F (Pi.single j 1) = 1 := fun j => by
    have h : F (Pi.single j 1) * F (Pi.single j 1) = F (Pi.single j 1) := by
      rw [← map_mul]; congr 1; ext k; by_cases hk : k = j <;> simp [hk]
    obtain h0 | h1 :=
      mul_eq_zero.mp (by rw [mul_sub, mul_one, h, sub_self] : F (Pi.single j 1) * (F (Pi.single j 1) - 1) = 0)
    ·
      exact Or.inl h0
    ·
      exact Or.inr (sub_eq_zero.mp h1)
  have hone : (∑ j, (Pi.single j (1 : Ω) : Fin d → Ω)) = 1 := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  have hsum : ∑ j, F (Pi.single j 1) = 1 := by
    rw [← map_sum, hone, map_one]
  obtain ⟨j, hj⟩ : ∃ j, F (Pi.single j 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ j, F (Pi.single j (1 : Ω)) = 0 := Finset.sum_eq_zero fun j _ => (hidem j).resolve_right (h j)
    rw [this] at hsum
    exact zero_ne_one hsum
  refine ⟨j, ?_⟩
  ext x
  have horth : ∀ k, k ≠ j → F (Pi.single k 1) = 0 := fun k hk => by
    have h0 : (Pi.single k (1 : Ω) : Fin d → Ω) * Pi.single j 1 = 0 := by
      ext l; by_cases hl : l = k <;> by_cases hl' : l = j <;> simp_all
    have := congrArg F h0
    rwa [map_mul, hj, mul_one, map_zero] at this
  have hx : x = ∑ k, x k • (Pi.single k (1 : Ω) : Fin d → Ω) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  rw [Pi.evalAlgHom_apply, hx, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun k _ hk => by rw [horth k hk, mul_zero]) (fun h => absurd (Finset.mem_univ j) h),
    Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ j) h)]
  simp [hj]

noncomputable def equivFinOfPi (Ω : Type*) [Field Ω] (d : ℕ) : ((Fin d → Ω) →ₐ[Ω] Ω) ≃ Fin d := by
  classical
  refine Equiv.ofBijective (fun F => (exists_eq_evalAlgHom F).choose) ⟨?_, ?_⟩
  ·
    intro F G h
    rw [(exists_eq_evalAlgHom F).choose_spec, (exists_eq_evalAlgHom G).choose_spec]
    exact congrArg _ h
  ·
    intro j
    refine ⟨Pi.evalAlgHom Ω (fun _ => Ω) j, ?_⟩
    have h := (exists_eq_evalAlgHom (Pi.evalAlgHom Ω (fun _ : Fin d => Ω) j)).choose_spec
    by_contra hne
    have := congrArg (fun F : (Fin d → Ω) →ₐ[Ω] Ω => F (Pi.single j 1)) h
    simp only [Pi.evalAlgHom_apply, Pi.single_eq_same] at this
    have hne' : (exists_eq_evalAlgHom (Pi.evalAlgHom Ω (fun _ : Fin d => Ω) j)).choose ≠ j := hne
    simp [hne'] at this

noncomputable def equivTensor (A : Type u) [CommRing A] (B : Type w) [CommRing B] [Algebra A B] (Ω : Type w') [Field Ω] [Algebra A Ω] : (B →ₐ[A] Ω) ≃ ((Ω ⊗[A] B) →ₐ[Ω] Ω) where
  toFun ψ := Algebra.TensorProduct.lift (AlgHom.id Ω Ω) ψ (fun _ _ => Commute.all _ _)
  invFun F := (F.restrictScalars A).comp Algebra.TensorProduct.includeRight
  left_inv ψ := by ext b; simp
  right_inv F := by
    apply Algebra.TensorProduct.ext'
    intro x b
    have hx : x ⊗ₜ[A] b = x • ((1 : Ω) ⊗ₜ[A] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [Algebra.TensorProduct.lift_tmul]
    show x * F ((1 : Ω) ⊗ₜ[A] b) = F (x ⊗ₜ[A] b)
    rw [hx, map_smul, smul_eq_mul]

noncomputable def tensorEquivPi {A : Type u} [CommRing A] {R' : Type v} [CommRing R'] [Algebra A R'] {B : Type w} [CommRing B] [Algebra A B] {d : ℕ} (φ : (R' ⊗[A] B) ≃ₐ[R'] (Fin d → R')) {Ω : Type w'} [Field Ω] [Algebra A Ω] (t₀ : R' →ₐ[A] Ω) : (Ω ⊗[A] B) ≃ₐ[Ω] (Fin d → Ω) := by
  let : Algebra R' Ω := t₀.toRingHom.toAlgebra
  have : IsScalarTower A R' Ω := IsScalarTower.of_algebraMap_eq fun a => (t₀.commutes a).symm
  exact (Algebra.TensorProduct.cancelBaseChange A R' Ω Ω B).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) φ).trans
      ((Algebra.TensorProduct.piRight R' Ω Ω (fun _ : Fin d => R')).trans
        (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R' Ω Ω)))

@[path]
private lemma main
  [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B] [Field Ω] [Algebra A Ω]
  {t₀ : R' →ₐ[A] Ω} {d : ℕ}
-- given
  (φ : (R' ⊗[A] B) ≃ₐ[R'] (Fin d → R')) :
-- imply
  Nonempty ((B →ₐ[A] Ω) ≃ Fin d) :=
-- proof
  ⟨(equivTensor A B Ω).trans (((tensorEquivPi φ t₀).arrowCongr AlgEquiv.refl).trans (equivFinOfPi Ω d))⟩


-- created on 2026-10-10
