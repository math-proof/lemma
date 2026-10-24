import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma one_tmul_smul {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [IsLocalRing R] (a : R) (m : M) : ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] (a • m) : IsLocalRing.ResidueField R ⊗[R] M) = (IsLocalRing.residue R a) • ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
private lemma one_tmul_smul_eq_zero {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [IsLocalRing R] {a : R} (ha : ¬ IsUnit a) (m : M) : ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] (a • m) : IsLocalRing.ResidueField R ⊗[R] M) = 0 := by
  rw [one_tmul_smul, (IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 ha), zero_smul]
/--
[LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
  (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  (f : M →ₗ[R] M) (hf : Function.Injective f) (r : ℕ)
  (hker : Module.finrank (IsLocalRing.ResidueField R) (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ r) :
  -- imply
  ∃ (n : ℕ) (b b' : Module.Basis (Fin n) R M) (a : Fin n → R) (s : Finset (Fin n)), (∀ i, f (b i) = a i • b' i) ∧ (∀ i ∉ s, IsUnit (a i)) ∧ s.card ≤ r := by
  -- proof
  classical
  set k := IsLocalRing.ResidueField R
  set n := Module.finrank R M
  let b₀ : Module.Basis (Fin n) R M := Module.finBasis R M
  let e : M ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  have hrank : Module.finrank R (LinearMap.range f) = Module.finrank R M := e.finrank_eq.symm
  obtain ⟨b', a, ab', hab'⟩ := Submodule.exists_smith_normal_form_of_rank_eq b₀ hrank
  let b : Module.Basis (Fin n) R M := ab'.map e.symm
  have hb : ∀ i, f (b i) = a i • b' i := by
    intro i
    have h1 : f (b i) = ((ab' i : LinearMap.range f) : M) := by
      change f (e.symm (ab' i)) = _
      have := LinearEquiv.ofInjective_apply f (h := hf) (e.symm (ab' i))
      rw [← this]
      simp [e]
    rw [h1, hab']
  refine ⟨n, b, b', a, Finset.univ.filter fun i => ¬ IsUnit (a i), hb, ?_, ?_⟩
  ·
    intro i hi
    by_contra h
    apply hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
  ·
    set s := Finset.univ.filter fun i => ¬ IsUnit (a i) with hs
    let bk : Module.Basis (Fin n) k (k ⊗[R] M) := Algebra.TensorProduct.basis k b
    have hmem : ∀ i : s, bk i ∈ LinearMap.ker (f.baseChange k) := by
      rintro ⟨i, hi⟩
      have hi' : ¬ IsUnit (a i) := (Finset.mem_filter.1 hi).2
      rw [LinearMap.mem_ker]
      change f.baseChange k (Algebra.TensorProduct.basis k b i) = 0
      rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, hb i]
      apply one_tmul_smul_eq_zero hi' (b' i)
    let u : s → LinearMap.ker (f.baseChange k) := fun i => ⟨bk i, hmem i⟩
    have hu : LinearIndependent k u := by
      apply LinearIndependent.of_comp (LinearMap.ker (f.baseChange k)).subtype
      change LinearIndependent k (fun i : s => bk i)
      apply bk.linearIndependent.comp _ Subtype.val_injective
    have hcard := hu.fintype_card_le_finrank
    rw [Fintype.card_coe] at hcard
    apply hcard.trans hker


-- created on 2026-10-20
